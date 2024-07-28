import Control.Monad
import qualified Data.Foldable as F
import qualified Data.Map.Strict as Map
import Data.Monoid
import qualified Data.IntMap.Lazy as IntMap
import qualified Data.IntSet as IntSet
import Data.List (intercalate)
import qualified Data.Set as Set
import Test.Hspec
import Test.QuickCheck

import Language.Grammar.Sequitur

main :: IO ()
main = hspec $ do
  describe "Sequitur.encode" $ do
    let cases = map (\(name, m) -> (name, Grammar m))
          [ ( "abab"
            , IntMap.fromList [(0, [NonTerminal 1, NonTerminal 1]), (1, [Terminal 'a', Terminal 'b'])]
            )
          , ( "abcab"
            , IntMap.fromList [(0, [NonTerminal 1, Terminal 'c', NonTerminal 1]), (1, [Terminal 'a', Terminal 'b'])]
            )
          , ( "abcabc"
            , IntMap.fromList [(0, [NonTerminal 2, NonTerminal 2]), (2, [Terminal 'a', Terminal 'b', Terminal 'c'])]
            )
          , ( "aaa"
            , IntMap.fromList [(0,[Terminal 'a', Terminal 'a', Terminal 'a'])]
            )
          , ( "baaabacaa"
            , IntMap.fromList [(0,[NonTerminal 1,NonTerminal 2,NonTerminal 1,Terminal 'c',NonTerminal 2]),(1,[Terminal 'b',Terminal 'a']),(2,[Terminal 'a',Terminal 'a'])]
            )
          ]
    forM_ cases $ \(xs, grammar) -> do
      it ("returns " ++ reprGrammar grammar ++ " for " ++ show xs) $ do
        encode xs `shouldBe` grammar

    it "returns a grammer with digram uniqueness property" $
      property $ forAll simpleString $ \s ->
        let g = encode s
         in counterexample (reprGrammar g) $ digramUniqueness g

    it "returns a grammer with rule utility property" $
      property $ forAll simpleString $ \s ->
        let g = encode s
         in counterexample (reprGrammar g) $ ruleUtility g

  describe "Sequitur.decode" $ do
    it "is the inverse of encode" $
      property $ forAll simpleString $ \s ->
        let g = encode s
            s' = decode g
         in counterexample (reprGrammar g) $ counterexample s' $ s == s'

    it "is lazy" $
      let g = Grammar $ IntMap.fromList [(0, [Terminal 'a', NonTerminal 1]), (1, undefined)]
          s = decode g
       in counterexample (reprGrammar g) $ head s `shouldBe` 'a'

  describe "Sequitur.decodeToSeq" $ do
    it "is equivalent to Sequitur.decode" $
      property $ forAll simpleString $ \s ->
        let g = encode s
         in counterexample (reprGrammar g) $ decode g === F.toList (decodeToSeq g)

  describe "Sequitur.decodeToMonoid" $ do
    it "can be used to compute length" $
      property $ forAll simpleString $ \s ->
        let g = encode s
         in counterexample (reprGrammar g) $ getSum (decodeToMonoid (\_ -> Sum 1) g) === length (decode g)

simpleString :: Gen String
simpleString = liftArbitrary (elements ['a'..'z'])

reprGrammar :: Grammar Char -> String
reprGrammar (Grammar m) = "{" ++ intercalate ", " [show nt ++ " -> " ++ intercalate " " (map reprSymbol body) | (nt, body) <- IntMap.toAscList m] ++ "}"
  where
    reprSymbol (Terminal c) = [c]
    reprSymbol (NonTerminal x) = show x

digramUniqueness :: Grammar Char -> Property
digramUniqueness (Grammar m) = conjoin
  [ counterexample (show ce) $
      case Set.toList ps of
        [_] -> True
        [(i1, j1), (i2, j2)] -> i1 == i2 && (j1 == j2 + 1 || j2 == j1 + 1)
        _ -> False
  | ce@(_digram, ps) <- Map.toList occurrences
  ]
  where
    occurrences = Map.fromListWith Set.union
      [ (digram, Set.singleton (i,j))
      | (i, body) <- IntMap.toList m, (j, digram) <- zip [(0::Int)..] (zip body (drop 1 body))
      ]

ruleUtility :: Grammar Char -> Property
ruleUtility (Grammar m) = 
  conjoin [counterexample (show (r, n)) $ n >= 2 | (r, n) <- IntMap.toList occurrences]
  .&&.
  IntMap.keysSet m === IntSet.insert 0 (IntMap.keysSet occurrences)
  where
    occurrences = IntMap.fromListWith (+)
      [(r, (1::Int)) | body <- IntMap.elems m, NonTerminal r <- body]
