module Project where

open import Haskell.Prelude

---- Quadrants

data Quadrant (a : Set) : Set where
  Leaf : a -> Quadrant a
  Node : Quadrant a -> Quadrant a -> Quadrant a -> Quadrant a -> Quadrant a
{-# COMPILE AGDA2HS Quadrant deriving (Show, Read, Eq) #-}

instance
  quadrantFunctor : Functor Quadrant
  quadrantFunctor .fmap fn (Leaf x) = Leaf (fn x) 
  quadrantFunctor .fmap fn (Node a b c d) = Node (fmap fn a) (fmap fn b) (fmap fn c) (fmap fn d)
{-# COMPILE AGDA2HS quadrantFunctor #-}

---- Functions for quadrant

fuse : {a : Set} -> {{eqA : Eq a}} 
        -> Quadrant a -> Quadrant a
fuse old@(Node (Leaf a) (Leaf b) (Leaf c) (Leaf d)) = if a == b && b == c && c == d then Leaf a else old
fuse old = old
{-# COMPILE AGDA2HS fuse #-}

depth : {a : Set} -> {{eqA : Eq a}} -> Quadrant a -> Nat
depth (Leaf x) = 0
depth (Node a b c d) = 1 + max (max (depth a) (depth b)) (max(depth c) (depth d))
{-# COMPILE AGDA2HS depth #-}

---- QuadTree

data QuadTree (a : Set) : Set where
  -- wrappedTree, treeLength, treeWidth, treeDepth
  Wrapper : Quadrant a -> Nat -> Nat -> Nat -> QuadTree a
{-# COMPILE AGDA2HS QuadTree #-}

instance
  quadTreeFunctor : Functor QuadTree
  quadTreeFunctor .fmap fn (Wrapper q l w d) = Wrapper (fmap fn q) l w d
{-# COMPILE AGDA2HS quadTreeFunctor #-}

---- Lenses

-- Eq a => combiner function -> CLens (Quadrant a) (Quadrant a)
lens_generic : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} 
         -> ((Quadrant a) -> (Quadrant a) -> (Quadrant a) -> (Quadrant a) -> (Quadrant a) -> (Quadrant a))
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lens_generic combine f (Node a b c d) = fmap (λ x -> fuse $ (combine a b c d x)) (f a)
lens_generic combine f l = fmap (λ x -> fuse $ (combine l l l l x)) (f l) where
{-# COMPILE AGDA2HS lens_generic #-}

-- Eq a => CLens (Quadrant a) (Quadrant a)
lens_a : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} 
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lens_a = lens_generic (λ a b c d x -> Node x b c d)
{-# COMPILE AGDA2HS lens_a #-}

-- Eq a => CLens (Quadrant a) (Quadrant a)
lens_b : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} 
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lens_b = lens_generic (λ a b c d x -> Node a x c d)
{-# COMPILE AGDA2HS lens_b #-}

-- Eq a => CLens (Quadrant a) (Quadrant a)
lens_c : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} 
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lens_c = lens_generic (λ a b c d x -> Node a b x d)
{-# COMPILE AGDA2HS lens_c #-}

-- Eq a => CLens (Quadrant a) (Quadrant a)
lens_d : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} 
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lens_d = lens_generic (λ a b c d x -> Node a b c x)
{-# COMPILE AGDA2HS lens_d #-}

---- Data access

infix -2 ifc_then_else_
ifc_then_else_ : {a : Set} → (c : Bool) → ({{IsTrue c}} → a) → ({{IsFalse c}} → a) → a
ifc false then x else y = y {{IsFalse.itsFalse}}
ifc true then x else y = x {{IsTrue.itsTrue}}
{-# COMPILE AGDA2HS ifc_then_else_ #-}

_^_ : Nat -> Nat -> Nat
_^_ b zero = 1
_^_ b (suc e) = b * (b ^ e)
-- Does not need compile, since it is already defined in haskell

getLocation : {a : Set} {{eqA : Eq a}} -> (Nat × Nat) -> QuadTree a -> a
getLocation (x , y) (Wrapper quad l w d) = go (x , y) d quad 
  where
    go : {a : Set} {{eqA : Eq a}} -> (Nat × Nat) -> Nat -> Quadrant a -> a
    go (x , y) _ (Leaf v) = v
    go (x , y) 0 node = temporary_impossible node where -- IMPOSSIBLE 
        temporary_impossible : {a : Set} {{eqA : Eq a}} -> Quadrant a -> a
        temporary_impossible (Leaf v) = v
        temporary_impossible (Node a b c d) = temporary_impossible a
    go (x , y) depth (Node a b c d) = 
      ifc y < mid then
        ifc x < mid then go (x , y) hn a
        else (λ {{x_gt_mid}} -> go (_-_ x mid {{x_gt_mid}} , y) hn b )
      else (λ {{y_gt_mid}} -> 
        ifc x < mid then go (x , _-_ y mid {{y_gt_mid}}) hn c
        else (λ {{x_gt_mid}} -> go (_-_ x mid {{x_gt_mid}} , _-_ y mid {{y_gt_mid}}) hn d ))
      where
        hn : Nat
        hn = ifc depth < 1 then 0 else depth - 1 -- depth < 1 is IMPOSSIBLE
        mid : Nat
        mid = 2 ^ hn   
{-# COMPILE AGDA2HS getLocation #-}