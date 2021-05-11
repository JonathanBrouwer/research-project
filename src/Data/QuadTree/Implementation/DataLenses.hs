{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}

module Data.QuadTree.Implementation.DataLenses where




import Data.Nat
import Data.Lens.Lens
import Data.Logic

import Data.QuadTree.Implementation.Definition
import Data.QuadTree.Implementation.ValidTypes
import Data.QuadTree.Implementation.QuadrantLenses

go :: Eq t => (Nat, Nat) -> Nat -> Lens (VQuadrant t) t
go _ Z = lensLeaf
go (x, y) (S deps)
  = if y < pow 2 deps then
      if x < pow 2 deps then
        lensA . go (mod x (pow 2 deps), mod y (pow 2 deps)) deps else
        lensB . go (mod x (pow 2 deps), mod y (pow 2 deps)) deps
      else
      if x < pow 2 deps then
        lensC . go (mod x (pow 2 deps), mod y (pow 2 deps)) deps else
        lensD . go (mod x (pow 2 deps), mod y (pow 2 deps)) deps

lensWrappedTree :: Eq t => Lens (VQuadTree t) (VQuadrant t)
lensWrappedTree fun (CVQuadTree (Wrapper (w, h) qd))
  = fmap
      (\case
           CVQuadrant qd₁ -> CVQuadTree (Wrapper (w, h) qd₁))
      (fun (CVQuadrant qd))

atLocation :: Eq t => (Nat, Nat) -> Nat -> Lens (VQuadTree t) t
atLocation index dep = lensWrappedTree . go index dep

