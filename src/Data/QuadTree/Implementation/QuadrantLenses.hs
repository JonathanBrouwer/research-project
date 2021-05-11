{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}

module Data.QuadTree.Implementation.QuadrantLenses where




import Data.Nat
import Data.Lens.Lens
import Data.Logic

import Data.QuadTree.Implementation.Definition
import Data.QuadTree.Implementation.ValidTypes

lensLeaf :: Eq t => Lens (VQuadrant t) t
lensLeaf f (CVQuadrant (Leaf v))
  = fmap (\ x -> CVQuadrant (Leaf x)) (f v)
lensLeaf x (CVQuadrant (Node qd qd₁ qd₂ qd₃))
  = error "lensLeaf: impossible"

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

lensA :: Eq t => Lens (VQuadrant t) (VQuadrant t)
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

lensB :: Eq t => Lens (VQuadrant t) (VQuadrant t)
lensB f (CVQuadrant (Leaf v))
  = fmap
      (\ x ->
         combine (CVQuadrant (Leaf v)) x (CVQuadrant (Leaf v))
           (CVQuadrant (Leaf v)))
      (f (CVQuadrant (Leaf v)))
lensB f (CVQuadrant (Node a b c d))
  = fmap
      (\ x -> combine (CVQuadrant a) x (CVQuadrant c) (CVQuadrant d))
      (f (CVQuadrant b))

lensC :: Eq t => Lens (VQuadrant t) (VQuadrant t)
lensC f (CVQuadrant (Leaf v))
  = fmap
      (\ x ->
         combine (CVQuadrant (Leaf v)) (CVQuadrant (Leaf v)) x
           (CVQuadrant (Leaf v)))
      (f (CVQuadrant (Leaf v)))
lensC f (CVQuadrant (Node a b c d))
  = fmap
      (\ x -> combine (CVQuadrant a) (CVQuadrant b) x (CVQuadrant d))
      (f (CVQuadrant c))

lensD :: Eq t => Lens (VQuadrant t) (VQuadrant t)
lensD f (CVQuadrant (Leaf v))
  = fmap
      (combine (CVQuadrant (Leaf v)) (CVQuadrant (Leaf v))
         (CVQuadrant (Leaf v)))
      (f (CVQuadrant (Leaf v)))
lensD f (CVQuadrant (Node a b c d))
  = fmap (combine (CVQuadrant a) (CVQuadrant b) (CVQuadrant c))
      (f (CVQuadrant d))

