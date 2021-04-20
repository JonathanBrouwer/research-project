module Project where

open import Haskell.Prelude

-- Quadrants

data Quadrant (a : Set) : Set where
  Leaf : a -> Quadrant a
  Node : Quadrant a -> Quadrant a -> Quadrant a -> Quadrant a -> Quadrant a
{-# COMPILE AGDA2HS Quadrant deriving (Show, Read, Eq) #-}

instance
  quadrantFunctor : Functor Quadrant
  quadrantFunctor .fmap fn (Leaf x) = Leaf (fn x) 
  quadrantFunctor .fmap fn (Node a b c d) = Node (fmap fn a) (fmap fn b) (fmap fn c) (fmap fn d)
{-# COMPILE AGDA2HS quadrantFunctor #-}

-- Functions for quadrant

fuse : {a : Set} -> {{eqA : Eq a}} 
        -> Quadrant a -> Quadrant a
fuse old@(Node (Leaf a) (Leaf b) (Leaf c) (Leaf d)) = if a == b && b == c && c == d then Leaf a else old
fuse old = old
{-# COMPILE AGDA2HS fuse #-}

-- Lenses for quadrant

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

-- QuadTree

data QuadTree (a : Set) : Set where
  Wrapper : Quadrant a -> Int -> Int -> Int -> QuadTree a

{-# COMPILE AGDA2HS QuadTree #-}
