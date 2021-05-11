module Data.QuadTree.Implementation.Definition where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Lens.Lens
open import Data.Logic

{-# FOREIGN AGDA2HS
{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
import Data.Nat
import Data.Lens.Lens
import Data.Logic
#-}

---- Quadrants
-- A quadrant is either a leaf or a node with 4 sub-quadrants

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
-- A quadtree is the width/height + the root quadrant

data QuadTree (t : Set) : Set where
  Wrapper : (Nat × Nat) -> Quadrant t -> QuadTree t
{-# COMPILE AGDA2HS QuadTree deriving (Show, Eq) #-}

instance
  quadTreeFunctor : Functor QuadTree
  quadTreeFunctor .fmap fn (Wrapper (w , h) q) = Wrapper (w , h) (fmap fn q) 
{-# COMPILE AGDA2HS quadTreeFunctor #-}