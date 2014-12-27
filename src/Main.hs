module Main where

import Language (parse)
import Template (compile, eval, runProg, showResults)

main :: IO ()
main = do contents <- readFile "test.txt"
          let (stack, dump, (size, free, cts), globals, stats) = compile . parse $ contents
          print cts
