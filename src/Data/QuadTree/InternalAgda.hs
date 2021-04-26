{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}

module Data.QuadTree.InternalAgda where

import Numeric.Natural (Natural)




import Data.QuadTree.Lens
import Data.QuadTree.Logic

data Quadrant t = Leaf t
                | Node (Quadrant t) (Quadrant t) (Quadrant t) (Quadrant t)
                    deriving (Show, Read, Eq)

instance Functor Quadrant where
    fmap fn (Leaf x) = Leaf (fn x)
    fmap fn (Node a b c d)
      = Node (fmap fn a) (fmap fn b) (fmap fn c) (fmap fn d)

data QuadTree t = Wrapper (Quadrant t) (Natural, Natural)
                    deriving (Show, Read, Eq)

instance Functor QuadTree where
    fmap fn (Wrapper q (w, h)) = Wrapper (fmap fn q) (w, h)

isCompressed :: Eq t => Quadrant t -> Bool
isCompressed (Leaf _) = True
isCompressed (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d))
  = not (a == b && b == c && c == d)
isCompressed (Node a b c d)
  = isCompressed a &&
      isCompressed b && isCompressed c && isCompressed d

depth :: Quadrant t -> Natural
depth (Leaf x) = 0
depth (Node a b c d)
  = 1 + max (max (depth a) (depth b)) (max (depth c) (depth d))

maxDepth :: QuadTree t -> Natural
maxDepth (Wrapper _ (w, h)) = log2up (max w h)

treeToQuadrant :: QuadTree t -> Quadrant t
treeToQuadrant (Wrapper qd _) = qd

isValid :: Eq t => Natural -> Quadrant t -> Bool
isValid dep qd = depth qd <= dep && isCompressed qd

newtype ValidQuadrant t = CValidQuadrant (Quadrant t)

newtype ValidQuadTree t = CValidQuadTree (QuadTree t)

combine ::
          Eq t =>
          ValidQuadrant t ->
            ValidQuadrant t ->
              ValidQuadrant t -> ValidQuadrant t -> ValidQuadrant t
combine (CValidQuadrant (Leaf va)) (CValidQuadrant (Leaf vb))
  (CValidQuadrant (Leaf vc)) (CValidQuadrant (Leaf vd))
  = ifc_then_else_
      (isCompressed (Node (Leaf va) (Leaf vb) (Leaf vc) (Leaf vd)))
      (CValidQuadrant (Node (Leaf va) (Leaf vb) (Leaf vc) (Leaf vd)))
      (CValidQuadrant (Leaf va))
combine (CValidQuadrant (Node v1 v2 v3 v4)) (CValidQuadrant b)
  (CValidQuadrant c) (CValidQuadrant d)
  = CValidQuadrant (Node (Node v1 v2 v3 v4) b c d)
combine (CValidQuadrant (Leaf va))
  (CValidQuadrant (Node v1 v2 v3 v4)) (CValidQuadrant c)
  (CValidQuadrant d)
  = CValidQuadrant (Node (Leaf va) (Node v1 v2 v3 v4) c d)
combine (CValidQuadrant (Leaf va)) (CValidQuadrant (Leaf vb))
  (CValidQuadrant (Node v1 v2 v3 v4)) (CValidQuadrant d)
  = CValidQuadrant (Node (Leaf va) (Leaf vb) (Node v1 v2 v3 v4) d)
combine (CValidQuadrant (Leaf va)) (CValidQuadrant (Leaf vb))
  (CValidQuadrant (Leaf vc)) (CValidQuadrant (Node v1 v2 v3 v4))
  = CValidQuadrant
      (Node (Leaf va) (Leaf vb) (Leaf vc) (Node v1 v2 v3 v4))

