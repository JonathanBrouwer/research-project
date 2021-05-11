{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}

module Data.QuadTree.Implementation.ValidTypes where




import Data.Nat
import Data.Lens.Lens
import Data.Logic

import Data.QuadTree.Implementation.Definition

depth :: Quadrant t -> Nat
depth (Leaf x) = 0
depth (Node a b c d)
  = 1 + max4 (depth a) (depth b) (depth c) (depth d)

maxDepth :: QuadTree t -> Nat
maxDepth (Wrapper (w, h) _) = log2up (max w h)

treeToQuadrant :: QuadTree t -> Quadrant t
treeToQuadrant (Wrapper _ qd) = qd

isCompressed :: Eq t => Quadrant t -> Bool
isCompressed (Leaf _) = True
isCompressed (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d))
  = not (a == b && b == c && c == d)
isCompressed (Node a b c d)
  = isCompressed a &&
      isCompressed b && isCompressed c && isCompressed d

isValid :: Eq t => Nat -> Quadrant t -> Bool
isValid dep qd = depth qd <= dep && isCompressed qd

newtype VQuadrant t = CVQuadrant (Quadrant t)

newtype VQuadTree t = CVQuadTree (QuadTree t)

qtToSafe :: Eq t => QuadTree t -> VQuadTree t
qtToSafe qt = CVQuadTree qt

qtFromSafe :: Eq t => VQuadTree t -> QuadTree t
qtFromSafe (CVQuadTree qt) = qt

