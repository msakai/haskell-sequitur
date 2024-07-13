{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Grammar.Sequitur
  (
  -- * Basic type definition
    Symbol (..)
  , RuleId
  , Grammar

  -- * High-level API
  , encode

  -- * Low-level monadic API
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
import Data.Function (on)
import Data.Hashable
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Primitive.MutVar
import qualified Data.HashTable.Class as H (toList)
import qualified Data.HashTable.ST.Cuckoo as H
import GHC.Generics (Generic)
import GHC.Stack

-- -------------------------------------------------------------------

type RuleId = Int

data Symbol a
  = NonTerminal !RuleId
  | Terminal !a
  deriving (Eq, Ord, Show, Generic)

instance (Hashable a) => Hashable (Symbol a)

type Digram a = (Symbol a, Symbol a)

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

data Builder s a
  = Builder
  { sRoot :: !(Rule s a)
  , sDigrams :: !(H.HashTable s (Digram a) (Node s a))
  , sRules :: !(H.HashTable s RuleId (Rule s a))
  , sRuleIdCounter :: {-# UNPACK #-} !(MutVar s Int)
  , sDummyNode :: !(Node s a)
  }

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

add :: (PrimMonad m, Hashable a) => Builder (PrimState m) a -> a -> m ()
add s a = do
  lastNode <- getLastNodeOfRule (sRoot s)
  _ <- insertAfter s lastNode (Terminal a)
  _ <- check s lastNode
  return ()

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

encode :: Hashable a => [a] -> Grammar a
encode xs = runST $ do
  e <- newBuilder
  mapM_ (add e) xs
  build e

-- -------------------------------------------------------------------
