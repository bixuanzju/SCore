module Main where

import Language
import Template
import Utils

main :: IO ()
main = do contents <- readFile "test.txt"
          let (stack, dump, (size, free, cts), globals, stats) = compile . parse $ contents
          print cts
