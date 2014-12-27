module Main where

import Language (parse, pprint)
import Template (compile, eval, runProg, showResults)

main :: IO ()
main = do contents <- readFile "test.txt"
          -- let (stack, dump, (size, free, cts), globals, stats) = compile . parse $ contents
          putStrLn $ runProg contents
          -- print . parse $  contents
