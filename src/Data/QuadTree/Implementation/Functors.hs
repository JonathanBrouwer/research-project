{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}

module Data.QuadTree.Implementation.Functors where




import Data.Nat
import Data.Lens.Lens
import Data.Logic
import Data.QuadTree.Implementation.Definition
import Data.QuadTree.Implementation.ValidTypes
import Data.QuadTree.Implementation.QuadrantLenses

class FunctorEq f where
    fmapₑ :: Eq a => Eq b => (a -> b) -> f a -> f b

type VQuadTreeDep t = VQuadTree t

quadtreeFunctor :: Nat -> FunctorEq VQuadTreeDep
quadtreeFunctor dep
  Data.QuadTree.Implementation.Functors.FunctorEq.fmapₑ fn
  (CVQuadTree (Wrapper (w, h) qd)) = toQt (fmapₑ fn (CVQuadrant qd))
  where
    toQt :: VQuadrant b -> VQuadTree b
    toQt (CVQuadrant qd₁) = CVQuadTree (Wrapper (w, h) qd₁)

