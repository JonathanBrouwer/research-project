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

depth :: Quadrant t -> Natural
depth (Leaf x) = 0
depth (Node a b c d)
  = 1 + max (max (depth a) (depth b)) (max (depth c) (depth d))

maxDepth :: QuadTree t -> Natural
maxDepth (Wrapper _ (w, h)) = log2up (max w h)

treeToQuadrant :: QuadTree t -> Quadrant t
treeToQuadrant (Wrapper qd _) = qd

newtype ValidQuadrant t = CValidQuadrant (Quadrant t)

newtype ValidQuadTree t = CValidQuadTree (QuadTree t)

fuse :: Eq t => ValidQuadrant t -> ValidQuadrant t
fuse (CValidQuadrant (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d)))
  = if a == b && b == c && c == d then CValidQuadrant (Leaf a) else
      CValidQuadrant (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d))
fuse old = old

lensWrappedTree ::
                  Eq t => CLens (ValidQuadTree t) (ValidQuadrant t)
lensWrappedTree fun (CValidQuadTree (Wrapper qd (w, h)))
  = fmap
      (\case
           CValidQuadrant qd₁ -> CValidQuadTree (Wrapper qd₁ (w, h)))
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
           (combine x (CValidQuadrant b) (CValidQuadrant c)
              (CValidQuadrant d)))
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
           (combine (CValidQuadrant a) x (CValidQuadrant c)
              (CValidQuadrant d)))
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
           (combine (CValidQuadrant a) (CValidQuadrant b) x
              (CValidQuadrant d)))
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
           (combine (CValidQuadrant a) (CValidQuadrant b) (CValidQuadrant c)
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

makeTreeAgda :: Eq t => (Natural, Natural) -> t -> ValidQuadTree t
makeTreeAgda (w, h) v = CValidQuadTree (Wrapper (Leaf v) (w, h))

atLocationAgda ::
                 Eq t => (Natural, Natural) -> Natural -> CLens (ValidQuadTree t) t
atLocationAgda index dep = lensWrappedTree . go index dep

getLocationAgda ::
                  Eq t => (Natural, Natural) -> Natural -> ValidQuadTree t -> t
getLocationAgda index dep = view (atLocationAgda index dep)

setLocationAgda ::
                  Eq t =>
                  (Natural, Natural) ->
                    Natural -> t -> ValidQuadTree t -> ValidQuadTree t
setLocationAgda index dep = set (atLocationAgda index dep)

mapLocationAgda ::
                  Eq t =>
                  (Natural, Natural) ->
                    Natural -> (t -> t) -> ValidQuadTree t -> ValidQuadTree t
mapLocationAgda index dep = over (atLocationAgda index dep)

invalidQuadTree = error "Invalid quadtree given"

qtToAgda :: Eq t => QuadTree t -> ValidQuadTree t
qtToAgda qt
  = ifc_then_else_ ((depth $ treeToQuadrant qt) <= maxDepth qt)
      (CValidQuadTree qt)
      invalidQuadTree

qtFromAgda :: Eq t => ValidQuadTree t -> QuadTree t
qtFromAgda (CValidQuadTree qt) = qt

makeTree :: Eq t => (Natural, Natural) -> t -> QuadTree t
makeTree size v = qtFromAgda $ makeTreeAgda size v

getLocation :: Eq t => (Natural, Natural) -> QuadTree t -> t
getLocation loc qt
  = getLocationAgda loc (maxDepth qt) $ qtToAgda qt

setLocation ::
              Eq t => (Natural, Natural) -> t -> QuadTree t -> QuadTree t
setLocation loc v qt
  = qtFromAgda $ setLocationAgda loc (maxDepth qt) v $ qtToAgda qt

mapLocation ::
              Eq t => (Natural, Natural) -> (t -> t) -> QuadTree t -> QuadTree t
mapLocation loc f qt
  = qtFromAgda $ mapLocationAgda loc (maxDepth qt) f $ qtToAgda qt

