module Main where

import Data.QuadTree

main :: IO ()
main = putStr ""

a = makeTree (100,100) '.'
b = setLocation (1,1) 'x' a