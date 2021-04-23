module Data.QuadTree.Logic where

import Numeric.Natural (Natural)

ifc_then_else_ :: Bool -> a -> a -> a
ifc_then_else_ False x y = y
ifc_then_else_ True x y = x

matchnat_ifzero_ifsuc_ :: Natural -> a -> a -> a
matchnat_ifzero_ifsuc_ x t f = ifc_then_else_ (x == 0) t f

pow :: Natural -> Natural -> Natural
pow b e = ifc_then_else_ (e == 0) 1 (b * pow b (e - 1))

log2up :: Natural -> Natural
log2up x = if x <= 1 then 0 else 1 + log2up (div x 2)

