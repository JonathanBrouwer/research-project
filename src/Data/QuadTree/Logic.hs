module Data.QuadTree.Logic where

import Data.Nat

ifc_then_else_ :: Bool -> a -> a -> a
ifc_then_else_ False x y = y
ifc_then_else_ True x y = x

pow :: Nat -> Nat -> Nat
pow b Z = 1
pow b (S e) = b * pow b e

log2up :: Nat -> Nat
log2up Z = 0
log2up (S Z) = 0
log2up x = S (log2up (div (x + 1) 2))

impossible = error "Impossible"

