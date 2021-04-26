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
    fmap fn (Leaf x₁) = Leaf (fn x₁)
    fmap fn (Node a b c d)
      = Node (fmap fn a) (fmap fn b) (fmap fn c) (fmap fn d)

data QuadTree t = Wrapper (Quadrant t) (Nat, Nat)
                    deriving (Show, Eq)

instance Functor QuadTree where
    fmap fn (Wrapper q (w, h)) = Wrapper (fmap fn q) (w, h)

isCompressed :: Eq t => Quadrant t -> Bool
isCompressed (Leaf _) = True
isCompressed (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d))
  = not (a == b && b == c && c == d)
isCompressed (Node a b c d)
  = isCompressed a &&
      isCompressed b && isCompressed c && isCompressed d

depth :: Quadrant t -> Nat
depth (Leaf x₁) = 0
depth (Node a b c d)
  = 1 + max (max (depth a) (depth b)) (max (depth c) (depth d))

maxDepth :: QuadTree t -> Nat
maxDepth (Wrapper _ (w, h)) = log2up (max w h)

treeToQuadrant :: QuadTree t -> Quadrant t
treeToQuadrant (Wrapper qd _) = qd

isValid :: Eq t => Nat -> Quadrant t -> Bool
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

lensWrappedTree ::
                  Eq t => CLens (ValidQuadTree t) (ValidQuadrant t)
lensWrappedTree fun (CValidQuadTree (Wrapper qd (w, h)))
  = fmap
      (\case
           CValidQuadrant qd₁ -> CValidQuadTree (Wrapper qd₁ (w, h)))
      (fun (CValidQuadrant qd))

lensA :: Eq t => CLens (ValidQuadrant t) (ValidQuadrant t)
lensA f (CValidQuadrant (Leaf v))
  = fmap
      (\ x ->
         combine x (CValidQuadrant (Leaf v)) (CValidQuadrant (Leaf v))
           (CValidQuadrant (Leaf v)))
      (f (CValidQuadrant (Leaf v)))
lensA f (CValidQuadrant (Node a b c d))
  = fmap
      (\ x ->
         combine x (CValidQuadrant b) (CValidQuadrant c) (CValidQuadrant d))
      (f (CValidQuadrant a))

lensB :: Eq t => CLens (ValidQuadrant t) (ValidQuadrant t)
lensB f (CValidQuadrant (Leaf v))
  = fmap
      (\ x ->
         combine (CValidQuadrant (Leaf v)) x (CValidQuadrant (Leaf v))
           (CValidQuadrant (Leaf v)))
      (f (CValidQuadrant (Leaf v)))
lensB f (CValidQuadrant (Node a b c d))
  = fmap
      (\ x ->
         combine (CValidQuadrant a) x (CValidQuadrant c) (CValidQuadrant d))
      (f (CValidQuadrant b))

lensC :: Eq t => CLens (ValidQuadrant t) (ValidQuadrant t)
lensC f (CValidQuadrant (Leaf v))
  = fmap
      (\ x ->
         combine (CValidQuadrant (Leaf v)) (CValidQuadrant (Leaf v)) x
           (CValidQuadrant (Leaf v)))
      (f (CValidQuadrant (Leaf v)))
lensC f (CValidQuadrant (Node a b c d))
  = fmap
      (\ x ->
         combine (CValidQuadrant a) (CValidQuadrant b) x (CValidQuadrant d))
      (f (CValidQuadrant c))

lensD :: Eq t => CLens (ValidQuadrant t) (ValidQuadrant t)
lensD f (CValidQuadrant (Leaf v))
  = fmap
      (combine (CValidQuadrant (Leaf v)) (CValidQuadrant (Leaf v))
         (CValidQuadrant (Leaf v)))
      (f (CValidQuadrant (Leaf v)))
lensD f (CValidQuadrant (Node a b c d))
  = fmap
      (combine (CValidQuadrant a) (CValidQuadrant b) (CValidQuadrant c))
      (f (CValidQuadrant d))

lensLeaf :: Eq t => CLens (ValidQuadrant t) t
lensLeaf f (CValidQuadrant (Leaf v))
  = fmap (\ x -> CValidQuadrant (Leaf x)) (f v)
lensLeaf x₁ (CValidQuadrant (Node qd qd₁ qd₂ qd₃))
  = error "lensLeaf: impossible"

go :: Eq t => (Nat, Nat) -> Nat -> CLens (ValidQuadrant t) t
go (x₁, y) Z = lensLeaf
go (x₁, y) (S deps)
  = ifc_then_else_ (y < mid)
      (ifc_then_else_ (x₁ < mid) (lensA . go (x₁, y) deps)
         (lensB . go (x₁ - mid, y) deps))
      (ifc_then_else_ (x₁ < mid) (lensC . go (x₁, y - mid) deps)
         (lensD . go (x₁ - mid, y - mid) deps))
  where
    mid :: Nat
    mid = pow 2 deps

makeTreeAgda :: Eq t => (Nat, Nat) -> t -> ValidQuadTree t
makeTreeAgda (w, h) v = CValidQuadTree (Wrapper (Leaf v) (w, h))

atLocationAgda ::
                 Eq t => (Nat, Nat) -> Nat -> CLens (ValidQuadTree t) t
atLocationAgda index dep = lensWrappedTree . go index dep

getLocationAgda ::
                  Eq t => (Nat, Nat) -> Nat -> ValidQuadTree t -> t
getLocationAgda index dep = view (atLocationAgda index dep)

setLocationAgda ::
                  Eq t =>
                  (Nat, Nat) -> Nat -> t -> ValidQuadTree t -> ValidQuadTree t
setLocationAgda index dep = set (atLocationAgda index dep)

mapLocationAgda ::
                  Eq t =>
                  (Nat, Nat) -> Nat -> (t -> t) -> ValidQuadTree t -> ValidQuadTree t
mapLocationAgda index dep = over (atLocationAgda index dep)

invalidQuadTree = error "Invalid quadtree given"

qtToAgda :: Eq t => QuadTree t -> ValidQuadTree t
qtToAgda qt
  = ifc_then_else_
      ((depth $ treeToQuadrant qt) <= maxDepth qt &&
         (isCompressed $ treeToQuadrant qt))
      (CValidQuadTree qt)
      invalidQuadTree

qtFromAgda :: Eq t => ValidQuadTree t -> QuadTree t
qtFromAgda (CValidQuadTree qt) = qt

makeTree :: Eq t => (Nat, Nat) -> t -> QuadTree t
makeTree size v = qtFromAgda $ makeTreeAgda size v

getLocation :: Eq t => (Nat, Nat) -> QuadTree t -> t
getLocation loc qt
  = getLocationAgda loc (maxDepth qt) $ qtToAgda qt

setLocation :: Eq t => (Nat, Nat) -> t -> QuadTree t -> QuadTree t
setLocation loc v qt
  = qtFromAgda $ setLocationAgda loc (maxDepth qt) v $ qtToAgda qt

mapLocation ::
              Eq t => (Nat, Nat) -> (t -> t) -> QuadTree t -> QuadTree t
mapLocation loc f qt
  = qtFromAgda $ mapLocationAgda loc (maxDepth qt) f $ qtToAgda qt

