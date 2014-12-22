module Main where

import Language

main :: IO ()
main = do contents <- readFile "test.txt"
          putStrLn $ pprint $ parse contents
