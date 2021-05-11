{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}

module Data.QuadTree.Implementation.Definition where




import Data.Nat
import Data.Lens.Lens
import Data.Logic

data Quadrant t = Leaf t
                | Node (Quadrant t) (Quadrant t) (Quadrant t) (Quadrant t)
                    deriving (Show, Eq)

instance Functor Quadrant where
    fmap fn (Leaf x) = Leaf (fn x)
    fmap fn (Node a b c d)
      = Node (fmap fn a) (fmap fn b) (fmap fn c) (fmap fn d)

data QuadTree t = Wrapper (Nat, Nat) (Quadrant t)
                    deriving (Show, Eq)

instance Functor QuadTree where
    fmap fn (Wrapper (w, h) q) = Wrapper (w, h) (fmap fn q)

