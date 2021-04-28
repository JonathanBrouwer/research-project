module Data.QuadTree.InternalAgda where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.QuadTree.Lens
open import Data.QuadTree.Logic
open import Data.QuadTree.PropDepthRelation

{-# FOREIGN AGDA2HS
{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
import Data.Nat
import Data.QuadTree.Lens
import Data.QuadTree.Logic
#-}

---- Quadrants

data Quadrant (t : Set) : Set where
  Leaf : t -> Quadrant t
  Node : Quadrant t -> Quadrant t -> Quadrant t -> Quadrant t -> Quadrant t
{-# COMPILE AGDA2HS Quadrant deriving (Show, Eq) #-}

instance
  quadrantFunctor : Functor Quadrant
  quadrantFunctor .fmap fn (Leaf x) = Leaf (fn x)
  quadrantFunctor .fmap fn (Node a b c d) = Node (fmap fn a) (fmap fn b) (fmap fn c) (fmap fn d)
{-# COMPILE AGDA2HS quadrantFunctor #-}

---- QuadTree

data QuadTree (t : Set) : Set where
  -- wrappedTree, (width x height)
  Wrapper : Quadrant t -> (Nat × Nat) -> QuadTree t
{-# COMPILE AGDA2HS QuadTree deriving (Show, Eq) #-}

instance
  quadTreeFunctor : Functor QuadTree
  quadTreeFunctor .fmap fn (Wrapper q (w , h)) = Wrapper (fmap fn q) (w , h)
{-# COMPILE AGDA2HS quadTreeFunctor #-}

maxDepth : {t : Set} -> QuadTree t -> Nat
maxDepth (Wrapper _ (w , h)) = log2up (max w h)
{-# COMPILE AGDA2HS maxDepth #-}

---- Fuse

combine : {t : Set} {{eqT : Eq t}}
  -> (a b c d : Quadrant t)
  -> Quadrant t
combine a@(Leaf va) b@(Leaf vb) c@(Leaf vc) d@(Leaf vd)
  = if (va == vb && vb == vc && vc == vd)
    then a
    else Node a b c d

-- Next 4 cases are the same, but agda is annoying
combine a b c d = (Node a b c d)
{-# COMPILE AGDA2HS combine #-}

---- Lenses

lensWrappedTree : {t : Set} {{eqT : Eq t}}
  -> CLens (QuadTree t) (Quadrant t)
lensWrappedTree fun (Wrapper qd (w , h)) = 
  fmap 
    (λ qd → (Wrapper qd (w , h)))
    (fun qd)
{-# COMPILE AGDA2HS lensWrappedTree #-}

lensLeaf : {t : Set} {{eqT : Eq t}}
  -> CLens (Quadrant t) t
lensLeaf f (Leaf v) = fmap Leaf (f v)
lensLeaf f (Node a b c d) = impossible --TODO: Impossible
{-# COMPILE AGDA2HS lensLeaf #-}

lensA : 
  {t : Set} {{eqT : Eq t}}
  -> CLens (Quadrant t) (Quadrant t)
lensA f l@(Leaf v) = 
  fmap (λ x -> combine x l l l ) (f l)
lensA f (Node a b c d) = 
  fmap (λ x -> combine x b c d ) (f a)
{-# COMPILE AGDA2HS lensA #-}

lensB : 
  {t : Set} {{eqT : Eq t}}
  -> CLens (Quadrant t) (Quadrant t)
lensB f l@(Leaf v) = 
  fmap (λ x -> combine l x l l ) (f l)
lensB f (Node a b c d) = 
  fmap (λ x -> combine a x c d ) (f b)
{-# COMPILE AGDA2HS lensB #-}

lensC : 
  {t : Set} {{eqT : Eq t}}
  -> CLens (Quadrant t) (Quadrant t)
lensC f l@(Leaf v) = 
  fmap (λ x -> combine l l x l ) (f l)
lensC f (Node a b c d) = 
  fmap (λ x -> combine a b x d ) (f c)
{-# COMPILE AGDA2HS lensC #-}

lensD : 
  {t : Set} {{eqT : Eq t}}
  -> CLens (Quadrant t) (Quadrant t)
lensD f l@(Leaf v) = 
  fmap (λ x -> combine l l l x ) (f l)
lensD f (Node a b c d) = 
  fmap (λ x -> combine a b c x ) (f d)
{-# COMPILE AGDA2HS lensD #-}

---- Data access

go : {t : Set} {{eqT : Eq t}}
  -> (Nat × Nat) -> (dep : Nat)
  -> CLens (Quadrant t) t
go _ Z = lensLeaf
go (x , y) (S deps) = ifc (y < mid) 
  then (ifc x < mid 
    then (             lensA ∘ go (x                 , y                ) deps)
    else (λ {{xgt}} -> lensB ∘ go (_-_ x mid {{xgt}} , y                ) deps))
  else (λ {{ygt}} -> (ifc x < mid
    then (             lensC ∘ go (x                 , _-_ y mid {{ygt}}) deps)
    else (λ {{xgt}} -> lensD ∘ go (_-_ x mid {{xgt}} , _-_ y mid {{ygt}}) deps)))
  where
    mid = pow 2 deps
{-# COMPILE AGDA2HS go #-}

---- Agda safe functions

makeTree : {t : Set} {{eqT : Eq t}} -> (size : Nat × Nat) -> (v : t) -> QuadTree t
makeTree (w , h) v = Wrapper (Leaf v) (w , h)
{-# COMPILE AGDA2HS makeTree #-}

atLocation : {t : Set} {{eqT : Eq t}}
  -> (Nat × Nat)
  -> CLens (QuadTree t) t
atLocation index f qt = (lensWrappedTree ∘ (go index (maxDepth qt))) f qt
{-# COMPILE AGDA2HS atLocation #-}

getLocation : {t : Set} {{eqT : Eq t}}
  -> (Nat × Nat)
  -> QuadTree t -> t
getLocation index = view (atLocation index)
{-# COMPILE AGDA2HS getLocation #-}

setLocation : {t : Set} {{eqT : Eq t}}
  -> (Nat × Nat)
  -> t -> QuadTree t -> QuadTree t
setLocation index = set (atLocation index)
{-# COMPILE AGDA2HS setLocation #-}

mapLocation : {t : Set} {{eqT : Eq t}}
  -> (Nat × Nat)
  -> (t -> t) -> QuadTree t -> QuadTree t
mapLocation index = over (atLocation index)
{-# COMPILE AGDA2HS mapLocation #-}