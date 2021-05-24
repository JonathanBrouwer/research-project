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

data QuadTree t = Wrapper (Nat, Nat) (Quadrant t)
                    deriving (Show, Eq)

