module Data.Logic where

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
log2up (S (S x)) = S (log2up (div (S (S (S x))) 2))

max4 :: Nat -> Nat -> Nat -> Nat -> Nat
max4 a b c d = max (max a b) (max c d)

sub :: Nat -> Nat -> Nat
sub a Z = a
sub (S a) (S b) = sub a b
sub Z (S b) = error "sub: impossible"

diff :: Nat -> Nat -> Nat
diff a Z = a
diff Z b = b
diff (S a) (S b) = diff a b

