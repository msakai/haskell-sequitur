{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
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
-- of the original sequence and can be used for data compression.
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
-- /SEQUITUR/ consumes input symbols one-by-one and appends each symbol at the end of the
-- grammar's start production (@S@ in the above example), then substitutes repeating
-- patterns in the given sequence with new rules. /SEQUITUR/ maintains two invariants:
--
--   [/Digram Uniqueness/]: /SEQUITUR/ ensures that no digram
--   (a.k.a. bigram) occurs more than once in the grammar. If a digram
--   (e.g. @ab@) occurs twice, SEQUITUR introduces a fresh non-terminal
--   symbol (e.g. @M@) and a rule (e.g. @M@ → @ab@) and replaces the
--   original occurrences with the newly introduced non-terminal symbol.
--   One exception is the cases where two occurrences overlap.
--
--   [/Rule Utility/]: If a non-terminal symbol occurs only once,
--   /SEQUITUR/ removes the associated rule and substitutes the occurrence
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
    Grammar (..)
  , Symbol (..)
  , NonTerminalSymbol
  , IsTerminalSymbol

  -- * Construction

  -- ** High-level API
  --
  -- | Use 'encode' if the entire sequence is given at once and you
  -- only need to create a single grammar from it.
  , encode

  -- ** Low-level monadic API
  --
  -- | Use these low-level monadic API if the input sequence is given
  -- incrementally, or you want to repeatedly construct grammars with
  -- newly added inputs.
  , Builder
  , newBuilder
  , add
  , build

  -- * Conversion to other types
  , decode
  , decodeToSeq
  , decodeToMonoid
  , decodeNonTerminalsToMonoid
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
#if MIN_VERSION_primitive(0,8,0)
import Data.Primitive.PrimVar
#endif
import qualified Data.HashTable.Class as H (toList)
import qualified Data.HashTable.ST.Cuckoo as H
import Data.Maybe
import Data.Semigroup (Endo (..))
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.String (IsString (..))
import GHC.Generics (Generic)
#if MIN_VERSION_base(4,17,0)
import qualified GHC.IsList as IsList (IsList (..))
#else
import qualified GHC.Exts as IsList (IsList (..))
#endif
import GHC.Stack

#if !MIN_VERSION_primitive(0,8,0)

type PrimVar s a = MutVar s a

{-# INLINE newPrimVar #-}
newPrimVar :: PrimMonad m => a -> m (PrimVar (PrimState m) a)
newPrimVar = newMutVar

{-# INLINE readPrimVar #-}
readPrimVar :: PrimMonad m => PrimVar (PrimState m) a -> m a
readPrimVar = readMutVar

{-# INLINE modifyPrimVar #-}
modifyPrimVar :: PrimMonad m => PrimVar (PrimState m) a -> (a -> a) -> m ()
modifyPrimVar = modifyMutVar'

#endif

-- -------------------------------------------------------------------

sanityCheck :: Bool
sanityCheck = False

-- -------------------------------------------------------------------

-- | Non-terminal symbols are represented by 'Int'.
--
-- The number @0@ is reserved for the start symbol of the grammar.
type NonTerminalSymbol = Int

-- | Internal alias of 'NonTerminalSymbol'
type RuleId = NonTerminalSymbol

-- | A symbol is either a terminal symbol (from a user-specified type)
-- or a non-terminal symbol.
data Symbol a
  = NonTerminal !NonTerminalSymbol
  | Terminal a
  deriving (Eq, Ord, Show, Generic)

instance (Hashable a) => Hashable (Symbol a)

-- | @since 0.2.0.0
instance Functor Symbol where
  fmap _ (NonTerminal rid) = NonTerminal rid
  fmap f (Terminal a) = Terminal (f a)

type Digram a = (Symbol a, Symbol a)

-- | Since a grammar generated by /SEQUITUR/ has exactly one rule for
-- each non-terminal symbol, a grammar is represented as a mapping
-- from non-terminal symbols (left-hand sides of the rules) to
-- sequences of symbols (right-hand side of the rules).
--
-- For example, a grammar
--
--   - @0@ → @1 1 2@
--
--   - @1@ → @2 2@
--
--   - @2@ → @a b c@
--
-- is represented as
--
-- @
-- Grammar (fromList
--   [ (0, [NonTerminal 1, NonTerminal 1, NonTerminal 2])
--   , (1, [NonTerminal 2, NonTerminal 2])
--   , (2, [Terminal \'a\', Terminal \'b\', Terminal \'c\'])
--   ])
-- @
--
-- Since a grammar generated by /SEQUITUR/ produces exactly one
-- sequence, we can identify the grammar with the produced
-- sequence. Therefore, 'Grammar' type is an instance of 'Foldable',
-- 'IsList.IsList', and 'IsString'.
newtype Grammar a = Grammar {unGrammar :: IntMap [Symbol a]}
  deriving (Eq, Show)

-- | @since 0.2.0.0
instance Functor Grammar where
  fmap f (Grammar m) = Grammar (fmap (map (fmap f)) m)

-- | @since 0.2.0.0
instance Foldable Grammar where
  foldMap = decodeToMonoid

-- | @since 0.2.0.0
instance IsTerminalSymbol a => IsList.IsList (Grammar a) where
  type Item (Grammar a) = a
  fromList = encode
  toList = decode

-- | @since 0.2.0.0
instance  IsString (Grammar Char) where
  fromString = encode

-- | @IsTerminalSymbol@ is a class synonym for absorbing the difference
-- between @hashable@ @<1.4.0.0@ and @>=1.4.0.0@.
--
-- @hashable-1.4.0.0@ makes 'Eq' be a superclass of 'Hashable'.
-- Therefore we define
--
-- @
-- type IsTerminalSymbol a = Hashable a
-- @
--
-- on @hashable >=1.4.0.0@, while we define
--
-- @
-- type IsTerminalSymbol a = (Eq a, Hashable a)
-- @
--
-- on @hashable <1.4.0.0@.
--
-- Also, developers can temporarily add other classes (e.g. 'Show') to
-- ease debugging.
#if MIN_VERSION_hashable(1,4,0)
type IsTerminalSymbol a = Hashable a
#else
type IsTerminalSymbol a = (Eq a, Hashable a)
#endif

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

getPrev :: Node s a -> ST s (Node s a)
getPrev node = readMutVar (nodePrev node)

getNext :: Node s a -> ST s (Node s a)
getNext node = readMutVar (nodeNext node)

setPrev :: Node s a -> Node s a -> ST s ()
setPrev node prev = writeMutVar (nodePrev node) prev

setNext :: Node s a -> Node s a -> ST s ()
setNext node next = writeMutVar (nodeNext node) next

mkGuardNode :: RuleId -> ST s (Node s a)
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
  , ruleRefCounter :: {-# UNPACK #-} !(PrimVar s Int)
  }

instance Eq (Rule s a) where
  (==) = (==) `on` ruleId

instance Hashable (Rule s a) where
  hashWithSalt salt rule = hashWithSalt salt (ruleId rule)

getFirstNodeOfRule :: Rule s a -> ST s (Node s a)
getFirstNodeOfRule rule = getNext (ruleGuardNode rule)

getLastNodeOfRule :: Rule s a -> ST s (Node s a)
getLastNodeOfRule rule = getPrev (ruleGuardNode rule)

mkRule :: RuleId -> ST s (Rule s a)
mkRule rid = do
  g <- mkGuardNode rid
  refCounter <- newPrimVar 0
  return $ Rule rid g refCounter

newRule :: Builder s a -> ST s (Rule s a)
newRule s = do
  rid <- readPrimVar (sRuleIdCounter s)
  modifyPrimVar (sRuleIdCounter s) (+ 1)
  rule <- mkRule rid
  H.insert (sRules s) rid rule
  return rule

-- -------------------------------------------------------------------

-- | 'Builder' denotes an internal state of the /SEQUITUR/ algorithm.
data Builder s a
  = Builder
  { sRoot :: !(Rule s a)
  , sDigrams :: !(H.HashTable s (Digram a) (Node s a))
  , sRules :: !(H.HashTable s RuleId (Rule s a))
  , sRuleIdCounter :: {-# UNPACK #-} !(PrimVar s Int)
  , sDummyNode :: !(Node s a)
  }

-- | Create a new 'Builder'.
newBuilder :: PrimMonad m => m (Builder (PrimState m) a)
newBuilder = stToPrim $ do
  root <- mkRule 0
  digrams <- H.new
  rules <- H.new
  counter <- newPrimVar 1

  prevRef <- newMutVar undefined
  nextRef <- newMutVar undefined
  let dummyNode = Node prevRef nextRef (Left 0)
  writeMutVar prevRef dummyNode
  writeMutVar nextRef dummyNode

  return $ Builder root digrams rules counter dummyNode

getRule :: HasCallStack => Builder s a -> RuleId -> ST s (Rule s a)
getRule s rid = do
  ret <- H.lookup (sRules s) rid
  case ret of
    Nothing -> error "getRule: invalid rule id"
    Just rule -> return rule

-- | Add a new symbol to the end of grammar's start production,
-- and perform normalization to keep the invariants of the /SEQUITUR/ algorithm.
add :: (PrimMonad m, IsTerminalSymbol a) => Builder (PrimState m) a -> a -> m ()
add s a = stToPrim $ do
  lastNode <- getLastNodeOfRule (sRoot s)
  _ <- insertAfter s lastNode (Terminal a)
  _ <- check s lastNode
  when sanityCheck $ do
    checkDigramTable s
    checkRefCount s

-- | Retrieve a grammar (as a persistent data structure) from the 'Builder'\'s internal state.
build :: (PrimMonad m) => Builder (PrimState m) a -> m (Grammar a)
build s = stToPrim $ do
  root <- freezeGuardNode $ ruleGuardNode (sRoot s)
  xs <- H.toList (sRules s)
  m <- forM xs $ \(rid, rule) -> do
    ys <- freezeGuardNode (ruleGuardNode rule)
    return (rid, ys)
  return $ Grammar $ IntMap.insert 0 root $ IntMap.fromList m

freezeGuardNode :: forall a s. Node s a -> ST s [Symbol a]
freezeGuardNode g = f [] =<< getPrev g
  where
    f :: [Symbol a] -> Node s a -> ST s [Symbol a]
    f ret node = do
      if isGuardNode node then
        return ret
      else do
        node' <- getPrev node
        f (nodeSymbol node : ret) node'

-- -------------------------------------------------------------------

link :: IsTerminalSymbol a => Builder s a -> Node s a -> Node s a -> ST s ()
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
        H.insert (sDigrams s) (sym2, sym3) right
      _ -> return ()

    case (nodeSymbolMaybe leftPrev, nodeSymbolMaybe left, nodeSymbolMaybe leftNext) of
      (Just sym1, Just sym2, Just sym3) | sym1 == sym2 && sym2 == sym3 ->
        H.insert (sDigrams s) (sym1, sym2) leftPrev
      _ -> return ()

  setNext left right
  setPrev right left

insertAfter :: (IsTerminalSymbol a, HasCallStack) => Builder s a -> Node s a -> Symbol a -> ST s (Node s a)
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
      modifyPrimVar (ruleRefCounter rule) (+ 1)

  return newNode

deleteDigram :: IsTerminalSymbol a => Builder s a -> Node s a -> ST s ()
deleteDigram s n
  | isGuardNode n = return ()
  | otherwise = do
      next <- getNext n
      unless (isGuardNode next) $ do
        _ <- H.mutate (sDigrams s) (nodeSymbol n, nodeSymbol next) $ \case
          Just n' | n /= n' -> (Just n', ())
          _ -> (Nothing, ())
        return ()

check :: IsTerminalSymbol a => Builder s a -> Node s a -> ST s Bool
check s node
  | isGuardNode node = return False
  | otherwise = do
      next <- getNext node
      if isGuardNode next then
        return False
      else do
        ret <- H.mutate (sDigrams s) (nodeSymbol node, nodeSymbol next) $ \case
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

match :: (IsTerminalSymbol a, HasCallStack) => Builder s a -> Node s a -> Node s a -> ST s ()
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
      H.insert (sDigrams s) (nodeSymbol node1, nodeSymbol node2) node1
      return rule

  firstNode <- getFirstNodeOfRule rule
  case nodeSymbol firstNode of
    Terminal _ -> return ()
    NonTerminal rid -> do
      rule2 <- getRule s rid
      freq <- readPrimVar (ruleRefCounter rule2)
      when (freq == 1) $ expand s firstNode rule2

  when sanityCheck $ do
    let loop node
          | isGuardNode node = return ()
          | otherwise = do
              case nodeSymbol node of
                Terminal _ -> return ()
                NonTerminal rid -> do
                  rule2 <- getRule s rid
                  freq <- readPrimVar (ruleRefCounter rule2)
                  when (freq <= 1) $ error "Sequitur.match: non-first node with refCount <= 1"
    loop =<< getNext firstNode

deleteNode :: (IsTerminalSymbol a, HasCallStack) => Builder s a -> Node s a -> ST s ()
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
      modifyPrimVar (ruleRefCounter rule) (subtract 1)

substitute :: (IsTerminalSymbol a, HasCallStack) => Builder s a -> Node s a -> Rule s a -> ST s ()
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

expand :: IsTerminalSymbol a => Builder s a -> Node s a -> Rule s a -> ST s ()
expand s node rule = do
  left <- getPrev node
  right <- getNext node
  deleteNode s node

  f <- getFirstNodeOfRule rule
  l <- getLastNodeOfRule rule
  link s left f
  link s l right

  n <- getNext l
  let key = (nodeSymbol l, nodeSymbol n)
  when sanityCheck $ do
    ret <- H.lookup (sDigrams s) key
    when (isJust ret) $ error "Sequitur.expand: the digram is already in the table"
  H.insert (sDigrams s) key l
  H.delete (sRules s) (ruleId rule)

-- -------------------------------------------------------------------

-- | Construct a grammar from a given sequence of symbols using /SEQUITUR/.
--
-- 'IsList.fromList' and 'fromString' can also be used.
encode :: IsTerminalSymbol a => [a] -> Grammar a
encode xs = runST $ do
  e <- newBuilder
  mapM_ (add e) xs
  build e

-- | Reconstruct an input sequence from a grammar.
--
-- It is lazy in the sense that you can consume from the beginning
-- before constructing the entire sequence. This function is suitable
-- if you just need to access the resulting sequence only once and
-- from beginning to end. If you need to use the resulting sequence in
-- a more complex way, 'decodeToSeq' would be more suitable.
--
-- This is a left-inverse of 'encode', and is equivalent to 'F.toList'
-- of 'Foldable' class and 'IsList.toList' of 'IsList.IsList'.
decode :: HasCallStack => Grammar a -> [a]
decode g = appEndo (decodeToMonoid (\a -> Endo (a :)) g) []

-- | A variant of 'decode' in which the result type is 'Seq'.
decodeToSeq :: HasCallStack => Grammar a -> Seq a
decodeToSeq = decodeToMonoid Seq.singleton

-- | 'Monoid'-based folding over the decoded sequence.
--
-- This function is equivalent to the following definition but is more
-- efficient due to the utilization of sharing.
--
-- @
-- decodeToMonoid f = 'mconcat' . 'map' f . 'decode'
-- @
--
-- This is equivalent to 'F.foldMap' of 'Foldable' class.
decodeToMonoid :: (Monoid m, HasCallStack) => (a -> m) -> Grammar a -> m
decodeToMonoid e g =  get 0 (decodeNonTerminalsToMonoid e g)

-- | 'Monoid'-based folding over the decoded sequence of each non-terminal symbol.
--
-- For example, in the following grammar
--
-- @
-- g = Grammar (IntMap.fromList
--   [ (0, [NonTerminal 1, Terminal \'c\', NonTerminal 1])
--   , (1, [Terminal \'a\', Terminal \'b\'])
--   ])
-- @
--
-- non-terminal symbol @0@ and @1@ produces @"abcab"@ and @"ab"@ respectively.
-- Therefore, @'decodeNonTerminalsToMonoid' f@ yields
--
-- @
-- IntMap.fromList
--   [ (0, mconcat (map f "abcab"))
--   , (1, mconcat (map f "ab"))
--   ]
-- @
decodeNonTerminalsToMonoid :: (Monoid m, HasCallStack) => (a -> m) -> Grammar a -> IntMap m
decodeNonTerminalsToMonoid e (Grammar m) = table
  where
    -- depends on the fact that fmap of IntMap is lazy
    table = fmap (mconcat . map f) m

    f (Terminal a) = e a
    f (NonTerminal r) = get r table

get :: HasCallStack => RuleId -> IntMap x -> x
get r tbl =
  case IntMap.lookup r tbl of
    Nothing -> error ("rule " ++ show r ++ " is missing")
    Just x -> x

-- -------------------------------------------------------------------

checkDigramTable :: IsTerminalSymbol a => Builder s a -> ST s ()
checkDigramTable s = do
  checkDigramTable1 s
  checkDigramTable2 s

checkDigramTable1 :: IsTerminalSymbol a => Builder s a -> ST s ()
checkDigramTable1 s = do
  ds <- H.toList (sDigrams s)
  forM_ ds $ \((sym1, sym2), node1) -> do
    node2 <- getNext node1
    unless ((nodeData node1, nodeData node2) == (Right sym1, Right sym2)) $ do
      error "checkDigramTable1: an entry points to a different digram"
    let f n =
          case nodeData n of
            Right _ -> f =<< getPrev n
            Left rid -> do
              rule <- if rid == 0 then
                        return (sRoot s)
                      else do
                        ret <- H.lookup (sRules s) rid
                        case ret of
                          Nothing -> error "checkDigramTable1: an entry points to a digram in an invalid rule"
                          Just rule -> return rule
              unless (ruleGuardNode rule == n) $ do
                error "checkDigramTable1: an entry points to a digram in a inconsistent rule"
    f node1

checkDigramTable2 :: IsTerminalSymbol a => Builder s a -> ST s ()
checkDigramTable2 s = do
  rules <- H.toList (sRules s)
  forM_ (sRoot s : map snd rules) $ \rule -> do
    let f node1 = do
          node2 <- getNext node1
          unless (isGuardNode node2) $ do
            let sym1 = nodeSymbol node1
                sym2 = nodeSymbol node2
                normalCase = do
                  ret <- H.lookup (sDigrams s) (sym1, sym2)
                  case ret of
                    Nothing -> error "checkDigramTable2: digram does not in the digram table"
                    Just node | node1 /= node -> error "checkDigramTable2: digram entry points to a different node"
                    Just _ -> return ()
                  f node2
            if sym1 == sym2 then do
              node3 <- getNext node2
              case nodeData node3 of
                Right sym3 | sym1 == sym3 -> do
                  ret <- H.lookup (sDigrams s) (sym1, sym2)
                  case ret of
                    Nothing -> error "checkDigramTable2: digram does not in the digram table"
                    Just node | node1 /= node && node2 /= node -> error "checkDigramTable2: digram entry points to a different node"
                    Just _ -> return ()
                  f node3
                _ -> normalCase
            else do
              normalCase
    f =<< getFirstNodeOfRule rule

checkRefCount :: forall s a. Builder s a -> ST s ()
checkRefCount s = do
  Grammar m <- build s
  let occurences = IntMap.fromListWith (+) [(rid, 1) | body <- IntMap.elems m, NonTerminal rid <- body]
      f :: (RuleId, Rule s a) -> ST s ()
      f (_r, rule) = do
        actual <- readPrimVar (ruleRefCounter rule)
        let expected = IntMap.findWithDefault 0 (ruleId rule) occurences
        unless (actual == expected) $
          error ("rule " ++ show (ruleId rule) ++ " occurs " ++ show expected ++ " times,"
                 ++ " but its reference counter is " ++ show actual)
  H.mapM_ f (sRules s)

-- -------------------------------------------------------------------
