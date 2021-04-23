module Data.QuadTree.InternalAgda where

import Numeric.Natural (Natural)

import Data.QuadTree.Functors
import Data.QuadTree.Logic

data Quadrant t = Leaf t
                | Node (Quadrant t) (Quadrant t) (Quadrant t) (Quadrant t)
                    deriving (Show, Read, Eq)

instance Functor Quadrant where
    fmap fn (Leaf x) = Leaf (fn x)
    fmap fn (Node a b c d)
      = Node (fmap fn a) (fmap fn b) (fmap fn c) (fmap fn d)

data QuadTree t = Wrapper (Quadrant t) Natural Natural Natural
                    deriving (Show, Read, Eq)

instance Functor QuadTree where
    fmap fn (Wrapper q l w d) = Wrapper (fmap fn q) l w d

makeTree :: Eq t => (Natural, Natural) -> t -> QuadTree t
makeTree (w, h) v = Wrapper (Leaf v) w h (log2up (max w h))

depth :: Quadrant t -> Natural
depth (Leaf x) = 0
depth (Node a b c d)
  = 1 + max (max (depth a) (depth b)) (max (depth c) (depth d))

isValidQuadTree :: Eq t => QuadTree t -> Bool
isValidQuadTree (Wrapper qd₁ _ _ d) = depth qd₁ <= d

data ValidQuadrant t = CValidQuadrant (Quadrant t)

data ValidQuadTree t = CValidQuadTree (QuadTree t)

qd :: Quadrant Bool
qd = Node (Leaf True) (Leaf True) (Leaf False) (Leaf False)

vqd :: ValidQuadrant Bool
vqd = CValidQuadrant qd

qt :: QuadTree Bool
qt = Wrapper qd 2 2 1

vqt :: ValidQuadTree Bool
vqt = CValidQuadTree qt

fuse :: Eq t => ValidQuadrant t -> ValidQuadrant t
fuse (CValidQuadrant (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d)))
  = if a == b && b == c && c == d then CValidQuadrant (Leaf a) else
      CValidQuadrant (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d))
fuse old = old

combine ::
          Eq t =>
          ValidQuadrant t ->
            ValidQuadrant t ->
              ValidQuadrant t -> ValidQuadrant t -> ValidQuadrant t
combine (CValidQuadrant a) (CValidQuadrant b) (CValidQuadrant c)
  (CValidQuadrant d) = CValidQuadrant (Node a b c d)

lensA ::
        Eq t =>
          Functor f =>
          Natural ->
            (ValidQuadrant t -> f (ValidQuadrant t)) ->
              ValidQuadrant t -> f (ValidQuadrant t)
lensA dep f (CValidQuadrant (Leaf v))
  = fmap
      (\ x ->
         fuse
           (combine x (CValidQuadrant (Leaf v)) (CValidQuadrant (Leaf v))
              (CValidQuadrant (Leaf v))))
      (f (CValidQuadrant (Leaf v)))
lensA dep f (CValidQuadrant (Node a b c d))
  = fmap
      (\ x ->
         fuse
           (combine x (CValidQuadrant a) (CValidQuadrant a)
              (CValidQuadrant a)))
      (f (CValidQuadrant a))

lensB ::
        Eq t =>
          Functor f =>
          Natural ->
            (ValidQuadrant t -> f (ValidQuadrant t)) ->
              ValidQuadrant t -> f (ValidQuadrant t)
lensB dep f (CValidQuadrant (Leaf v))
  = fmap
      (\ x ->
         fuse
           (combine (CValidQuadrant (Leaf v)) x (CValidQuadrant (Leaf v))
              (CValidQuadrant (Leaf v))))
      (f (CValidQuadrant (Leaf v)))
lensB dep f (CValidQuadrant (Node a b c d))
  = fmap
      (\ x ->
         fuse
           (combine (CValidQuadrant b) x (CValidQuadrant b)
              (CValidQuadrant b)))
      (f (CValidQuadrant b))

lensC ::
        Eq t =>
          Functor f =>
          Natural ->
            (ValidQuadrant t -> f (ValidQuadrant t)) ->
              ValidQuadrant t -> f (ValidQuadrant t)
lensC dep f (CValidQuadrant (Leaf v))
  = fmap
      (\ x ->
         fuse
           (combine (CValidQuadrant (Leaf v)) (CValidQuadrant (Leaf v)) x
              (CValidQuadrant (Leaf v))))
      (f (CValidQuadrant (Leaf v)))
lensC dep f (CValidQuadrant (Node a b c d))
  = fmap
      (\ x ->
         fuse
           (combine (CValidQuadrant c) (CValidQuadrant c) x
              (CValidQuadrant c)))
      (f (CValidQuadrant c))

lensD ::
        Eq t =>
          Functor f =>
          Natural ->
            (ValidQuadrant t -> f (ValidQuadrant t)) ->
              ValidQuadrant t -> f (ValidQuadrant t)
lensD dep f (CValidQuadrant (Leaf v))
  = fmap
      (\ x ->
         fuse
           (combine (CValidQuadrant (Leaf v)) (CValidQuadrant (Leaf v))
              (CValidQuadrant (Leaf v))
              x))
      (f (CValidQuadrant (Leaf v)))
lensD dep f (CValidQuadrant (Node a b c d))
  = fmap
      (\ x ->
         fuse
           (combine (CValidQuadrant d) (CValidQuadrant d) (CValidQuadrant d)
              x))
      (f (CValidQuadrant d))

