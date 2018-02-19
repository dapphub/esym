{-# Language NamedFieldPuns #-}

module EVM.Symbex.Main where

import System.Environment (getArgs)

import EVM.Assembly
import EVM.Symbex
import EVM.Symbex.Print

import qualified Dappsys.Weth

-- import Data.Generics.Uniplate.Data

import Data.Aeson (encode)
import qualified Data.ByteString as BS
import Data.Text.Encoding (encodeUtf8)
import Data.Text (pack)
import qualified Data.ByteString.Lazy.Char8 as B8
import qualified Data.ByteString.Base16 as BS16

import Text.Printf

showPath :: Path -> IO ()
showPath (Path x (State { storage }) o) = do
  putStrLn $ "** Conditions"
  -- mapM_ putStrLn (map (display . rewrite optimize) x)
  mapM_ putStrLn (map display x)
  putStrLn $ "\n** Outcome " ++ show o
  -- putStr "Stack:   "
  -- putStrLn $ "(" ++ intercalate " " (map (display . rewrite optimize) stack) ++ ")"
  -- putStr "Memory:  "
  -- putStrLn (display memory)
  -- putStrLn "\nMemory:  "
  -- putStrLn (display (rewriteBi (optimize :: AValue -> Maybe AValue) memory))
  -- putStr "Storage: "
  -- putStrLn (display storage)
  putStrLn "\n** Storage"
  -- putStrLn (display (rewriteBi (optimize :: AValue -> Maybe AValue) storage))
  putStrLn (display storage)
  putStrLn ""

emptyState :: State
emptyState = State
  { stack = []
  , pc = 0
  , memory = Null
  , storage = Null
  }

run :: Code -> [Path]
run code = step code emptyState

showPaths :: [Path] -> IO ()
showPaths = mapM_ f . zip [1..]
  where
    f (i, x) = do
      putStrLn $ "* Path " ++ show (i :: Int) ++ "\n"
      showPath x

main :: IO ()
main = do
  xs <- getArgs
  case xs of
    ["--bytecode", "weth"] -> do
      mapM_ (printf "%02x") (compile (assemble Dappsys.Weth.contract))
      putStrLn ""
    ["--read", x] ->
      case parse (BS.unpack (fst (BS16.decode (encodeUtf8 (pack x))))) of
        Nothing -> error "wtf"
        Just y ->
          showPaths (run y)
    _ -> do
      let
        (json, xs') =
          case xs of
            ("--json":_) -> (True, tail xs)
            _ -> (False, xs)
        thing =
          case xs' of
            ["weth"] -> assemble Dappsys.Weth.contract
            ["multisig"] -> multisig2
            _ -> error "wtf"

      if json
        then
          B8.putStrLn . encode $ step' thing emptyState
        else
          showPaths (run thing)
