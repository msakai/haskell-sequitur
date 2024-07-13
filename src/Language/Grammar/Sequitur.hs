{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Grammar.Sequitur
-- Copyright   :  (c) Masahiro Sakai 2024
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- /SEQUITUR/ is a linear-time, online algorithm for producing a context-free
-- grammar from an input sequence. The resulting grammar is a compact representation
-- of original sequence and can be used for data compression.
--
-- Example:
--
--   - Input string: @abcabcabcabcabc@
--
--   - Resulting grammar
--
--       - @S@ → @AAB@
--
--       - @A@ → @BB@
--
--       - @B@ → @abc@
--
-- /SEQUITUR/ consumes input symbols one-by-one and append each symbol at the end of the
-- grammar's start production (@S@ in the above example), then substitutes repeating
-- patterns in the given sequence with new rules. /SEQUITUR/ maintains two invariants:
--
--   [/Digram uniqueness/]: /SEQUITUR/ ensures that no digram
--   (a.k.a. bigram) occurs more than once in the grammar. If a digram
--   (e.g. @ab@) occurs twice, SEQUITUR introduce a fresh non-terminal
--   symbol (e.g. @M@) and a rule (e.g. @M@ → @ab@) and replace
--   original occurences with the newly introduced non-terminals.  One
--   exception is the cases where two occurrence overlap.
--
--   [/Rule Utility/]: If a non-terminal symbol occurs only once,
--   /SEQUITUR/ removes the associated rule and substitute the occurence
--   with the right-hand side of the rule.
--
-- References:
--
--   - [Sequitur algorithm - Wikipedia](https://en.m.wikipedia.org/wiki/Sequitur_algorithm)
--
--   - [sequitur.info](http://www.sequitur.info/)
--
--   - Nevill-Manning, C.G. and Witten, I.H. (1997) "[Identifying
--     Hierarchical Structure in Sequences: A linear-time
--     algorithm](https://doi.org/10.1613/jair.374)," Journal of
--     Artificial Intelligence Research, 7, 67-82.
--
-----------------------------------------------------------------------------
module Language.Grammar.Sequitur
  (
  -- * Basic type definition
    Grammar
  , RuleId
  , Symbol (..)

  -- * High-level API
  --
  -- Use these APIs if the entire sequence is given at once and you
  -- only need to create a single grammar from it.
  , encode
  , decode
  , decodeLazy
  , decodeToSeq
  , decodeToMonoid

  -- * Low-level monadic API
  --
  -- Use these low-level monadic API if the input sequence is given
  -- incrementally, or you want to re-construct grammar after you
  -- receive additinal inputs.
  , Builder
  , newBuilder
  , add
  , build
  ) where

import Control.Exception
import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import Data.Either
import qualified Data.Foldable as F
import Data.Function (on)
import Data.Hashable
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Primitive.MutVar
import qualified Data.HashTable.Class as H (toList)
import qualified Data.HashTable.ST.Cuckoo as H
import Data.Semigroup (Endo (..))
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import GHC.Generics (Generic)
import GHC.Stack

-- -------------------------------------------------------------------

-- | A non-terminal symbol is represented by an 'Int'.
--
-- The number @0@ is reserved for the start symbol of the grammar.
type RuleId = Int

-- | A symbol is either a terminal symbol (from user-specified type)
-- or a non-terminal symbol which we represent using 'RuleId' type.
data Symbol a
  = NonTerminal !RuleId
  | Terminal !a
  deriving (Eq, Ord, Show, Generic)

instance (Hashable a) => Hashable (Symbol a)

type Digram a = (Symbol a, Symbol a)

-- | A grammar is a mappping from non-terminal (left-hand side of the
-- rule) to sequnce of symbols (right hand side of the rule).
--
-- Non-terminal is represented as a 'RuleId'.
type Grammar a = IntMap [Symbol a]

-- -------------------------------------------------------------------

data Node s a
  = Node
  { nodePrev :: {-# UNPACK #-} !(MutVar s (Node s a))
  , nodeNext :: {-# UNPACK #-} !(MutVar s (Node s a))
  , nodeData :: Either RuleId (Symbol a)
  } deriving (Generic)

instance Eq (Node s a) where
  (==) = (==) `on` nodePrev

isGuardNode :: Node s a -> Bool
isGuardNode s = isLeft $ nodeData s

nodeSymbolMaybe :: Node s a -> Maybe (Symbol a)
nodeSymbolMaybe node =
  case nodeData node of
    Left _ -> Nothing
    Right sym -> Just sym

nodeSymbol :: HasCallStack => Node s a -> Symbol a
nodeSymbol node =
  case nodeSymbolMaybe node of
    Nothing -> error "nodeSymbol is called for guard node"
    Just sym -> sym

ruleOfGuardNode :: Node s a -> Maybe RuleId
ruleOfGuardNode node =
  case nodeData node of
    Left rule -> Just rule
    Right _ -> Nothing

getPrev :: PrimMonad m => Node (PrimState m) a -> m (Node (PrimState m) a)
getPrev node = readMutVar (nodePrev node)

getNext :: PrimMonad m => Node (PrimState m) a -> m (Node (PrimState m) a)
getNext node = readMutVar (nodeNext node)

setPrev :: PrimMonad m => Node (PrimState m) a -> Node (PrimState m) a -> m ()
setPrev node prev = writeMutVar (nodePrev node) prev

setNext :: PrimMonad m => Node (PrimState m) a -> Node (PrimState m) a -> m ()
setNext node next = writeMutVar (nodeNext node) next

mkGuardNode :: PrimMonad m => RuleId -> m (Node (PrimState m) a)
mkGuardNode rid = do
  prevRef <- newMutVar undefined
  nextRef <- newMutVar undefined
  let node = Node prevRef nextRef (Left rid)
  writeMutVar prevRef node
  writeMutVar nextRef node
  return node

-- -------------------------------------------------------------------

data Rule s a
  = Rule
  { ruleId :: {-# UNPACK #-} !RuleId
  , ruleGuardNode :: !(Node s a)
  , ruleRefCounter :: {-# UNPACK #-} !(MutVar s Int)
  }

instance Eq (Rule s a) where
  (==) = (==) `on` ruleId

instance Hashable (Rule s a) where
  hashWithSalt salt rule = hashWithSalt salt (ruleId rule)

getFirstNodeOfRule :: PrimMonad m => Rule (PrimState m) a -> m (Node (PrimState m) a)
getFirstNodeOfRule rule = getNext (ruleGuardNode rule)

getLastNodeOfRule :: PrimMonad m => Rule (PrimState m) a -> m (Node (PrimState m) a)
getLastNodeOfRule rule = getPrev (ruleGuardNode rule)

mkRule :: PrimMonad m => RuleId -> m (Rule (PrimState m) a)
mkRule rid = do
  g <- mkGuardNode rid
  refCounter <- newMutVar 0
  return $ Rule rid g refCounter

newRule :: PrimMonad m => Builder (PrimState m) a -> m (Rule (PrimState m) a)
newRule s = do
  rid <- readMutVar (sRuleIdCounter s)
  modifyMutVar' (sRuleIdCounter s) (+ 1)
  rule <- mkRule rid
  stToPrim $ H.insert (sRules s) rid rule
  return rule

-- -------------------------------------------------------------------

-- | 'Builder' denotes a internal state of the /SEQUITUR/ algorithm.
data Builder s a
  = Builder
  { sRoot :: !(Rule s a)
  , sDigrams :: !(H.HashTable s (Digram a) (Node s a))
  , sRules :: !(H.HashTable s RuleId (Rule s a))
  , sRuleIdCounter :: {-# UNPACK #-} !(MutVar s Int)
  , sDummyNode :: !(Node s a)
  }

-- | Create a new 'Builder'.
newBuilder :: PrimMonad m => m (Builder (PrimState m) a)
newBuilder = do
  root <- mkRule 0
  digrams <- stToPrim $ H.new
  rules <- stToPrim $ H.new
  counter <- newMutVar 1

  prevRef <- newMutVar undefined
  nextRef <- newMutVar undefined
  let dummyNode = Node prevRef nextRef (Left 0)
  writeMutVar prevRef dummyNode
  writeMutVar nextRef dummyNode

  return $ Builder root digrams rules counter dummyNode

getRule :: (PrimMonad m, HasCallStack) => Builder (PrimState m) a -> RuleId -> m (Rule (PrimState m) a)
getRule s rid = stToPrim $ do
  ret <- H.lookup (sRules s) rid
  case ret of
    Nothing -> error "getRule: invalid rule id"
    Just rule -> return rule

-- | Add a new symbol to the end of grammar's start production,
-- and perform normalization to keep the invariants of /SEQUITUR/ algorithm.
add :: (PrimMonad m, Hashable a) => Builder (PrimState m) a -> a -> m ()
add s a = do
  lastNode <- getLastNodeOfRule (sRoot s)
  _ <- insertAfter s lastNode (Terminal a)
  _ <- check s lastNode
  return ()

-- | Retrieve a grammar (as a persistent data structure) from 'Builder'\'s internal state.
build :: (PrimMonad m) => Builder (PrimState m) a -> m (Grammar a)
build s = do
  root <- freezeGuardNode $ ruleGuardNode (sRoot s)
  xs <- stToPrim $ H.toList (sRules s)
  m <- forM xs $ \(rid, rule) -> do
    ys <- freezeGuardNode (ruleGuardNode rule)
    return $ (rid, ys)
  return $ IntMap.insert 0 root $ IntMap.fromList m

freezeGuardNode :: forall a m. (PrimMonad m) => Node (PrimState m) a -> m [Symbol a]
freezeGuardNode g = f [] =<< getPrev g
  where
    f :: [Symbol a] -> Node (PrimState m) a -> m [Symbol a]
    f ret node = do
      if isGuardNode node then
        return ret
      else do
        node' <- getPrev node
        f (nodeSymbol node : ret) node'

-- -------------------------------------------------------------------

link :: (PrimMonad m, Hashable a) => Builder (PrimState m) a -> Node (PrimState m) a -> Node (PrimState m) a -> m ()
link s left right = do
  leftPrev <- getPrev left
  leftNext <- getNext left
  rightPrev <- getPrev right
  rightNext <- getNext right

  unless (isGuardNode leftNext) $ do
    deleteDigram s left

    -- これが不要なのは何故?
    -- unless (isGuardNode rightPrev) $ deleteDigram s rightPrev

    case (nodeSymbolMaybe rightPrev, nodeSymbolMaybe right, nodeSymbolMaybe rightNext) of
      (Just sym1, Just sym2, Just sym3) | sym1 == sym2 && sym2 == sym3 ->
        stToPrim $ H.insert (sDigrams s) (sym2, sym3) right
      _ -> return ()

    case (nodeSymbolMaybe leftPrev, nodeSymbolMaybe left, nodeSymbolMaybe leftNext) of
      (Just sym1, Just sym2, Just sym3) | sym1 == sym2 && sym2 == sym3 ->
        stToPrim $ H.insert (sDigrams s) (sym1, sym2) leftPrev
      _ -> return ()

  setNext left right
  setPrev right left

insertAfter :: (PrimMonad m, Hashable a, HasCallStack) => Builder (PrimState m) a -> Node (PrimState m) a -> Symbol a -> m (Node (PrimState m) a)
insertAfter s node sym = do
  prevRef <- newMutVar (sDummyNode s)
  nextRef <- newMutVar (sDummyNode s)
  let newNode = Node prevRef nextRef (Right sym)

  next <- getNext node
  link s newNode next
  link s node newNode

  case sym of
    Terminal _ -> return ()
    NonTerminal rid -> do
      rule <- getRule s rid
      modifyMutVar' (ruleRefCounter rule) (+ 1)

  return newNode

deleteDigram :: (PrimMonad m, Hashable a) => Builder (PrimState m) a -> Node (PrimState m) a -> m ()
deleteDigram s n
  | isGuardNode n = return ()
  | otherwise = do
      next <- getNext n
      unless (isGuardNode next) $ do
        _ <- stToPrim $ H.mutate (sDigrams s) (nodeSymbol n, nodeSymbol next) $ \case
          Just n' | n /= n' -> (Just n', ())
          _ -> (Nothing, ())
        return ()

check :: (PrimMonad m, Hashable a) => Builder (PrimState m) a -> Node (PrimState m) a -> m Bool
check s node
  | isGuardNode node = return False
  | otherwise = do
      next <- getNext node
      if isGuardNode next then
        return False
      else do
        ret <- stToPrim $ H.mutate (sDigrams s) (nodeSymbol node, nodeSymbol next) $ \case
          Nothing -> (Just node, Nothing)
          Just node' -> (Just node', Just node')
        case ret of
          Nothing -> return False
          Just node' -> do
             next' <- getNext node'
             if node == next' then
               return False
             else do
               match s node node'
               return True

match :: (PrimMonad m, Hashable a, HasCallStack) => Builder (PrimState m) a -> Node (PrimState m) a -> Node (PrimState m) a -> m ()
match s ss m = do
  mPrev <- getPrev m
  mNext <- getNext m
  mNextNext <- getNext mNext

  rule <- case ruleOfGuardNode mPrev of
    Just rid | isGuardNode mNextNext -> do
      rule <- getRule s rid
      substitute s ss rule
      return rule
    _ -> do
      rule <- newRule  s
      ss2 <- getNext ss
      lastNode <- getLastNodeOfRule rule
      node1 <- insertAfter s lastNode (nodeSymbol ss)
      node2 <- insertAfter s node1 (nodeSymbol ss2)
      substitute s m rule
      substitute s ss rule
      stToPrim $ H.insert (sDigrams s) (nodeSymbol node1, nodeSymbol node2) node1
      return rule

  firstNode <- getFirstNodeOfRule rule
  case nodeSymbol firstNode of
    Terminal _ -> return ()
    NonTerminal rid -> do
      rule2 <- getRule s rid
      freq <- readMutVar (ruleRefCounter rule2)
      when (freq == 1) $ expand s firstNode rule2

deleteNode :: (PrimMonad m, Hashable a, HasCallStack) => Builder (PrimState m) a -> Node (PrimState m) a -> m ()
deleteNode s node = do
  assert (not (isGuardNode node)) $ return ()
  prev <- getPrev node
  next <- getNext node
  link s prev next
  deleteDigram s node
  case nodeSymbol node of
    Terminal _ -> return ()
    NonTerminal rid -> do
      rule <- getRule s rid
      modifyMutVar' (ruleRefCounter rule) (subtract 1)

substitute :: (PrimMonad m, Hashable a, HasCallStack) => Builder (PrimState m) a -> Node (PrimState m) a -> Rule (PrimState m) a -> m ()
substitute s node rule = do
  prev <- getPrev node
  deleteNode s =<< getNext prev
  deleteNode s =<< getNext prev
  _ <- insertAfter s prev (NonTerminal (ruleId rule))
  ret <- check s prev
  unless ret $ do
    next <- getNext prev
    _ <- check s next
    return ()

expand :: (PrimMonad m, Hashable a) => Builder (PrimState m) a -> Node (PrimState m) a -> Rule (PrimState m) a -> m ()
expand s node rule = do
  left <- getPrev node
  right <- getNext node
  deleteNode s node

  f <- getFirstNodeOfRule rule
  l <- getLastNodeOfRule rule
  link s left f
  link s l right

  n <- getNext l
  stToPrim $ H.insert (sDigrams s) (nodeSymbol l, nodeSymbol n) l
  stToPrim $ H.delete (sRules s) (ruleId rule)

-- -------------------------------------------------------------------

-- | Construct a grammer from a given sequence of symbols using /SEQUITUR/.
encode :: Hashable a => [a] -> Grammar a
encode xs = runST $ do
  e <- newBuilder
  mapM_ (add e) xs
  build e

-- | Reconstruct a input sequence from a grammar.
--
-- This is a left-inverse of 'encode'.
--
-- This function is implemented as
--
-- @
-- decode = 'F.toList' . 'decodeToSeq'
-- @
--
-- and provided just for convenience.
-- For serious usage, use 'decodeToSeq' or 'decodeLazy'.
decode :: HasCallStack => Grammar a -> [a]
decode = F.toList . decodeToSeq

-- | A variant of 'decode' with possibly better performance.
decodeToSeq :: HasCallStack => Grammar a -> Seq a
decodeToSeq = decodeToMonoid Seq.singleton

-- | A variant of 'decode' but you can consume from the beginning
-- before constructing entire sequence.
decodeLazy :: HasCallStack => Grammar a -> [a]
decodeLazy g = appEndo (decodeToMonoid (\a -> Endo (a :)) g) []

-- | 'Monoid'-based folding over the decoded sequence.
--
-- This function is equivalent to the following definition, is more
-- efficent due to the utilization of sharing.b
--
-- @
-- decodeToMonoid f = 'mconcat' . 'map' f . 'decode'
-- @
decodeToMonoid :: (Monoid m, HasCallStack) => (a -> m) -> Grammar a -> m
decodeToMonoid e g = get 0 table
  where
    -- depends on the fact that fmap of IntMap is lazy
    table = fmap (mconcat . map f) g

    f (Terminal a) = e a
    f (NonTerminal r) = get r table

    get r tbl =
      case IntMap.lookup r tbl of
        Nothing -> error ("rule " ++ show r ++ " is missing")
        Just x -> x

-- -------------------------------------------------------------------
