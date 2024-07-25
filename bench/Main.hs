{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Criterion (bench, bgroup, env, nf, whnf)
import Criterion.Main (defaultMain)
import Data.Functor ((<&>))
import Language.Grammar.Sequitur (Symbol, encode)
import Test.QuickCheck (Arbitrary (arbitrary), generate, vectorOf)

main :: IO ()
main = do
  defaultMain
    [ bgroup "encoding runs in linear time" do
        [500, 1_000 .. 100_000] <&> \x ->
          env
            do generate (vectorOf x (arbitrary @Char))
            do bench ("size: " <> show x) . whnf encode
    ]
