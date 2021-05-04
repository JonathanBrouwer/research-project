{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}

module Data.QuadTree.InternalAgda where




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

lensWrappedTree :: Eq t => CLens (VQuadTree t) (VQuadrant t)
lensWrappedTree fun (CVQuadTree (Wrapper (w, h) qd))
  = fmap
      (\case
           CVQuadrant qd₁ -> CVQuadTree (Wrapper (w, h) qd₁))
      (fun (CVQuadrant qd))

lensLeaf :: Eq t => CLens (VQuadrant t) t
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

lensB :: Eq t => CLens (VQuadrant t) (VQuadrant t)
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

lensC :: Eq t => CLens (VQuadrant t) (VQuadrant t)
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

lensD :: Eq t => CLens (VQuadrant t) (VQuadrant t)
lensD f (CVQuadrant (Leaf v))
  = fmap
      (combine (CVQuadrant (Leaf v)) (CVQuadrant (Leaf v))
         (CVQuadrant (Leaf v)))
      (f (CVQuadrant (Leaf v)))
lensD f (CVQuadrant (Node a b c d))
  = fmap (combine (CVQuadrant a) (CVQuadrant b) (CVQuadrant c))
      (f (CVQuadrant d))

go :: Eq t => (Nat, Nat) -> Nat -> CLens (VQuadrant t) t
go _ Z = lensLeaf
go (x, y) (S deps)
  = ifc_then_else_ (y < mid) (lensA . go (mod x mid, mod y mid) deps)
      (lensC . go (mod x mid, mod y mid) deps)
  where
    mid :: Nat
    mid = pow 2 deps

atLocation :: Eq t => (Nat, Nat) -> Nat -> CLens (VQuadTree t) t
atLocation index dep = lensWrappedTree . go index dep

makeTreeSafe :: Eq t => (Nat, Nat) -> t -> VQuadTree t
makeTreeSafe (w, h) v = CVQuadTree (Wrapper (w, h) (Leaf v))

getLocationSafe :: Eq t => (Nat, Nat) -> Nat -> VQuadTree t -> t
getLocationSafe index dep = view (atLocation index dep)

setLocationSafe ::
                  Eq t => (Nat, Nat) -> Nat -> t -> VQuadTree t -> VQuadTree t
setLocationSafe index dep = set (atLocation index dep)

mapLocationSafe ::
                  Eq t => (Nat, Nat) -> Nat -> (t -> t) -> VQuadTree t -> VQuadTree t
mapLocationSafe index dep = over (atLocation index dep)

invQuadTree = error "Invalid quadtree given"

qtToSafe :: Eq t => QuadTree t -> VQuadTree t
qtToSafe qt
  = ifc_then_else_
      ((depth $ treeToQuadrant qt) <= maxDepth qt &&
         (isCompressed $ treeToQuadrant qt))
      (CVQuadTree qt)
      invQuadTree

qtFromSafe :: Eq t => VQuadTree t -> QuadTree t
qtFromSafe (CVQuadTree qt) = qt

makeTree :: Eq t => (Nat, Nat) -> t -> QuadTree t
makeTree size v = qtFromSafe $ makeTreeSafe size v

getLocation :: Eq t => (Nat, Nat) -> QuadTree t -> t
getLocation loc qt
  = getLocationSafe loc (maxDepth qt) $ qtToSafe qt

setLocation :: Eq t => (Nat, Nat) -> t -> QuadTree t -> QuadTree t
setLocation loc v qt
  = qtFromSafe $ setLocationSafe loc (maxDepth qt) v $ qtToSafe qt

mapLocation ::
              Eq t => (Nat, Nat) -> (t -> t) -> QuadTree t -> QuadTree t
mapLocation loc f qt
  = qtFromSafe $ mapLocationSafe loc (maxDepth qt) f $ qtToSafe qt

