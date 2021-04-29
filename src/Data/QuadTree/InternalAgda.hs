{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}

module Data.QuadTree.InternalAgda where




import Data.Nat
import Data.QuadTree.Lens
import Data.QuadTree.Logic

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

depth :: Quadrant t -> Nat
depth (Leaf x) = 0
depth (Node a b c d)
  = 1 + max4 (depth a) (depth b) (depth c) (depth d)

maxDepth :: QuadTree t -> Nat
maxDepth (Wrapper (w, h) _) = log2up (max w h)

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

lensWrappedTree :: Eq t => CLens (QuadTree t) (Quadrant t)
lensWrappedTree fun (Wrapper (w, h) qd)
  = fmap (\ qd -> Wrapper (w, h) qd) (fun qd)

lensLeaf :: Eq t => CLens (Quadrant t) t
lensLeaf f (Leaf v) = fmap Leaf (f v)
lensLeaf f (Node a b c d) = impossible

combine ::
          Eq t =>
          VQuadrant t ->
            VQuadrant t -> VQuadrant t -> VQuadrant t -> VQuadrant t
combine (CVQuadrant (Leaf va)) (CVQuadrant (Leaf vb))
  (CVQuadrant (Leaf vc)) (CVQuadrant (Leaf vd))
  = ifc_then_else_ (va == vb && vb == vc && vc == vd)
      (CVQuadrant (Leaf va))
      (CVQuadrant (Node (Leaf va) (Leaf vb) (Leaf vc) (Leaf vd)))
combine (CVQuadrant (Node v1 v2 v3 v4)) (CVQuadrant b)
  (CVQuadrant c) (CVQuadrant d)
  = CVQuadrant (Node (Node v1 v2 v3 v4) b c d)
combine (CVQuadrant (Leaf va)) (CVQuadrant (Node v1 v2 v3 v4))
  (CVQuadrant c) (CVQuadrant d)
  = CVQuadrant (Node (Leaf va) (Node v1 v2 v3 v4) c d)
combine (CVQuadrant (Leaf va)) (CVQuadrant (Leaf vb))
  (CVQuadrant (Node v1 v2 v3 v4)) (CVQuadrant d)
  = CVQuadrant (Node (Leaf va) (Leaf vb) (Node v1 v2 v3 v4) d)
combine (CVQuadrant (Leaf va)) (CVQuadrant (Leaf vb))
  (CVQuadrant (Leaf vc)) (CVQuadrant (Node v1 v2 v3 v4))
  = CVQuadrant
      (Node (Leaf va) (Leaf vb) (Leaf vc) (Node v1 v2 v3 v4))

lensA :: Eq t => CLens (VQuadrant t) (VQuadrant t)
lensA f (CVQuadrant (Leaf v))
  = fmap
      (\ x ->
         combine x (CVQuadrant (Leaf v)) (CVQuadrant (Leaf v))
           (CVQuadrant (Leaf v)))
      (f (CVQuadrant (Leaf v)))
lensA f (CVQuadrant (Node a b c d))
  = fmap
      (\ x -> combine x (CVQuadrant b) (CVQuadrant c) (CVQuadrant d))
      (f (CVQuadrant a))

