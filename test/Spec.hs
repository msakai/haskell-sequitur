import Control.Monad
import qualified Data.Map.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import Data.List (intercalate)
import qualified Data.Set as Set
import Test.Hspec
import Test.QuickCheck

import Language.Grammar.Sequitur

main :: IO ()
main = hspec $ do
  describe "Sequitur.encode" $ do
    let reprGrammar grammar = "{" ++ intercalate ", " [show nt ++ " -> " ++ intercalate " " (map reprSymbol body) | (nt, body) <- IntMap.toAscList grammar] ++ "}"
           where
             reprSymbol (Terminal c) = [c]
             reprSymbol (NonTerminal x) = show x
        cases =
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
            occurrences = Map.fromListWith Set.union [(digram, Set.singleton (i,j)) | (i, body) <- IntMap.toList g, (j, digram) <- zip [(0::Int)..] (zip body (tail body))]
            f ps = case Set.toList ps of
                     [_] -> True
                     [(i1, j1), (i2, j2)] -> i1 == i2 && (j1 == j2 + 1 || j2 == j1 + 1)
                     _ -> False
         in counterexample (reprGrammar g) $
            conjoin
            [ counterexample (show ce) $ f ps
            | ce@(_digram, ps) <- Map.toList occurrences
            ]

    it "returns a grammer with rule utilization property" $
      property $ forAll simpleString $ \s ->
        let g = encode s
            occurrences = IntMap.fromListWith (+) [(r, (1::Int)) | body <- IntMap.elems g, NonTerminal r <- body]
         in counterexample (reprGrammar g) $
            conjoin [counterexample (show (r, n)) $ n >= 2 | (r, n) <- IntMap.toList occurrences]

simpleString :: Gen String
simpleString = liftArbitrary (elements ['a'..'z'])
