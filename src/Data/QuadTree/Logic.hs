module Data.QuadTree.Logic where

import Data.Nat

ifc_then_else_ :: Bool -> a -> a -> a
ifc_then_else_ False x y = y
ifc_then_else_ True x y = x

pow :: Nat -> Nat -> Nat
pow b e = ifc_then_else_ (e == 0) 1 (b * pow b (e - 1))

log2up :: Nat -> Nat
log2up Z = 0
log2up (S Z) = 0
log2up x = S (log2up (div (x + 1) 2))

