{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}

module Data.QuadTree.Implementation.Folding where




import Data.Nat
import Data.Lens.Lens
import Data.Logic
import Data.QuadTree.Implementation.Definition
import Data.QuadTree.Implementation.ValidTypes
import Data.QuadTree.Implementation.QuadrantLenses

class FoldableEq t where
    foldEqMap :: Eq a => Eq b => Monoid b => (a -> b) -> t a -> b

