{-# OPTIONS_GHC -Wall #-}
module Main (main) where

import Control.Monad
import qualified Data.IntMap.Strict as IntMap
import Data.List (intercalate)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Language.Grammar.Sequitur as Sequitur
import Options.Applicative
import System.Clock
import Text.Printf


data Options
  = Options
  { optInputFile :: FilePath
  , optPrintGrammar :: Bool
  }

optionsParser :: Parser Options
optionsParser = Options
  <$> inputFile
  <*> printGrammar
  where
    inputFile = strArgument
      $  metavar "FILE"
      <> help "input filename"
    printGrammar = flag True False
      $  long "no-grammar"
      <> help "do not print resulting grammar"

parserInfo :: ParserInfo Options
parserInfo = info (optionsParser <**> helper)
  $  fullDesc
  <> header "sequitur-demo"

main :: IO ()
main = do
  opt <- execParser parserInfo

  -- To benchmark time without I/O, we read a file beforehand using strict I/O.
  s <- T.readFile (optInputFile opt)

  startCPU <- getTime ProcessCPUTime
  startWC  <- getTime Monotonic

  builder <- Sequitur.newBuilder
  forM_ (T.unpack s) $ \c -> do
    Sequitur.add builder c
  Sequitur.Grammar m <- Sequitur.build builder

  endCPU <- getTime ProcessCPUTime
  endWC  <- getTime Monotonic
  printf "cpu time = %.3fs\n" (durationSecs startCPU endCPU)
  printf "wall clock time = %.3fs\n" (durationSecs startWC endWC)

  when (optPrintGrammar opt) $ do
    forM_ (IntMap.toList m) $ \(r, body) -> do
      let f (Sequitur.Terminal c) = show c
          f (Sequitur.NonTerminal r') = show r'
      putStrLn $ show r ++ " -> " ++ intercalate " " (map f body)

  return ()

durationSecs :: TimeSpec -> TimeSpec -> Double
durationSecs start end = fromIntegral (toNanoSecs (end `diffTimeSpec` start)) / 10^(9::Int)
