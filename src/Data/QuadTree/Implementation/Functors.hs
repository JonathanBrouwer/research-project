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

