{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}

module Data.QuadTree.InternalAgda where

import Numeric.Natural (Natural)




import Data.QuadTree.Functors
import Data.QuadTree.Logic

type CLens s a = forall f. Functor f => (a -> f a) -> s -> f s

data Quadrant t = Leaf t
                | Node (Quadrant t) (Quadrant t) (Quadrant t) (Quadrant t)
                    deriving (Show, Read, Eq)

instance Functor Quadrant where
    fmap fn (Leaf x) = Leaf (fn x)
    fmap fn (Node a b c d)
      = Node (fmap fn a) (fmap fn b) (fmap fn c) (fmap fn d)

data QuadTree t = Wrapper (Quadrant t) Natural Natural
                    deriving (Show, Read, Eq)

instance Functor QuadTree where
    fmap fn (Wrapper q l w) = Wrapper (fmap fn q) l w

makeTree :: Eq t => (Natural, Natural) -> t -> QuadTree t
makeTree (w, h) v = Wrapper (Leaf v) w h

depth :: Quadrant t -> Natural
depth (Leaf x) = 0
depth (Node a b c d)
  = 1 + max (max (depth a) (depth b)) (max (depth c) (depth d))

treeToQuadrant :: QuadTree t -> Quadrant t
treeToQuadrant (Wrapper qd _ _) = qd

newtype ValidQuadrant t = CValidQuadrant (Quadrant t)

newtype ValidQuadTree t = CValidQuadTree (QuadTree t)

fuse :: Eq t => ValidQuadrant t -> ValidQuadrant t
fuse (CValidQuadrant (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d)))
  = if a == b && b == c && c == d then CValidQuadrant (Leaf a) else
      CValidQuadrant (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d))
fuse old = old

lensWrappedTree ::
                  Eq t => CLens (ValidQuadTree t) (ValidQuadrant t)
lensWrappedTree fun (CValidQuadTree (Wrapper qd l w))
  = fmap
      (\case
           CValidQuadrant qd₁ -> CValidQuadTree (Wrapper qd₁ l w))
      (fun (CValidQuadrant qd))

combine ::
          Eq t =>
          ValidQuadrant t ->
            ValidQuadrant t ->
              ValidQuadrant t -> ValidQuadrant t -> ValidQuadrant t
combine (CValidQuadrant a) (CValidQuadrant b) (CValidQuadrant c)
  (CValidQuadrant d) = CValidQuadrant (Node a b c d)

lensA :: Eq t => CLens (ValidQuadrant t) (ValidQuadrant t)
lensA f (CValidQuadrant (Leaf v))
  = fmap
      (\ x ->
         fuse
           (combine x (CValidQuadrant (Leaf v)) (CValidQuadrant (Leaf v))
              (CValidQuadrant (Leaf v))))
      (f (CValidQuadrant (Leaf v)))
lensA f (CValidQuadrant (Node a b c d))
  = fmap
      (\ x ->
         fuse
           (combine x (CValidQuadrant a) (CValidQuadrant a)
              (CValidQuadrant a)))
      (f (CValidQuadrant a))

lensB :: Eq t => CLens (ValidQuadrant t) (ValidQuadrant t)
lensB f (CValidQuadrant (Leaf v))
  = fmap
      (\ x ->
         fuse
           (combine (CValidQuadrant (Leaf v)) x (CValidQuadrant (Leaf v))
              (CValidQuadrant (Leaf v))))
      (f (CValidQuadrant (Leaf v)))
lensB f (CValidQuadrant (Node a b c d))
  = fmap
      (\ x ->
         fuse
           (combine (CValidQuadrant b) x (CValidQuadrant b)
              (CValidQuadrant b)))
      (f (CValidQuadrant b))

lensC :: Eq t => CLens (ValidQuadrant t) (ValidQuadrant t)
lensC f (CValidQuadrant (Leaf v))
  = fmap
      (\ x ->
         fuse
           (combine (CValidQuadrant (Leaf v)) (CValidQuadrant (Leaf v)) x
              (CValidQuadrant (Leaf v))))
      (f (CValidQuadrant (Leaf v)))
lensC f (CValidQuadrant (Node a b c d))
  = fmap
      (\ x ->
         fuse
           (combine (CValidQuadrant c) (CValidQuadrant c) x
              (CValidQuadrant c)))
      (f (CValidQuadrant c))

lensD :: Eq t => CLens (ValidQuadrant t) (ValidQuadrant t)
lensD f (CValidQuadrant (Leaf v))
  = fmap
      (\ x ->
         fuse
           (combine (CValidQuadrant (Leaf v)) (CValidQuadrant (Leaf v))
              (CValidQuadrant (Leaf v))
              x))
      (f (CValidQuadrant (Leaf v)))
lensD f (CValidQuadrant (Node a b c d))
  = fmap
      (\ x ->
         fuse
           (combine (CValidQuadrant d) (CValidQuadrant d) (CValidQuadrant d)
              x))
      (f (CValidQuadrant d))

lensLeaf :: Eq t => CLens (ValidQuadrant t) t
lensLeaf f (CValidQuadrant (Leaf v))
  = fmap (\ x -> CValidQuadrant (Leaf x)) (f v)
lensLeaf x (CValidQuadrant (Node qd qd₁ qd₂ qd₃))
  = error "lensLeaf: impossible"

toZeroMaxDepth = id

go ::
     Eq t => (Natural, Natural) -> Natural -> CLens (ValidQuadrant t) t
go (x, y) dep
  = matchnat_ifzero_ifsuc_ dep
      (\ g qd ->
         fmap
           (\case
                CValidQuadrant qd₁ -> CValidQuadrant qd₁)
           (lensLeaf g (toZeroMaxDepth qd)))
      (\ g vqd ->
         fmap
           (\case
                CValidQuadrant qd -> CValidQuadrant qd)
           (ifc_then_else_ (y < pow 2 (dep - 1))
              (ifc_then_else_ (x < pow 2 (dep - 1))
                 (lensA (go (x, y) (dep - 1) g))
                 (lensB (go (x - pow 2 (dep - 1), y) (dep - 1) g)))
              (ifc_then_else_ (x < pow 2 (dep - 1))
                 (lensC (go (x, y - pow 2 (dep - 1)) (dep - 1) g))
                 (lensD
                    (go (x - pow 2 (dep - 1), y - pow 2 (dep - 1)) (dep - 1) g)))
              (case vqd of
                   CValidQuadrant qd -> CValidQuadrant qd)))

atLocation ::
             Eq a => (Natural, Natural) -> Natural -> CLens (ValidQuadTree a) a
atLocation index dep = lensWrappedTree . go index dep

getLocationAgda ::
                  Eq a => (Natural, Natural) -> Natural -> ValidQuadTree a -> a
getLocationAgda index dep qt
  = getConst $ atLocation index dep CConst qt

setLocationAgda ::
                  Eq a =>
                  (Natural, Natural) ->
                    Natural -> a -> ValidQuadTree a -> ValidQuadTree a
setLocationAgda index dep v qt
  = runIdentity $ atLocation index dep (\ _ -> CIdentity v) qt

mapLocationAgda ::
                  Eq a =>
                  (Natural, Natural) ->
                    Natural -> (a -> a) -> ValidQuadTree a -> ValidQuadTree a
mapLocationAgda index dep f qt
  = runIdentity $ atLocation index dep (CIdentity . f) qt

