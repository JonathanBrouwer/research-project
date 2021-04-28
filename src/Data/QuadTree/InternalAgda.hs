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

data QuadTree t = Wrapper (Quadrant t) (Nat, Nat)
                    deriving (Show, Eq)

instance Functor QuadTree where
    fmap fn (Wrapper q (w, h)) = Wrapper (fmap fn q) (w, h)

maxDepth :: QuadTree t -> Nat
maxDepth (Wrapper _ (w, h)) = log2up (max w h)

combine ::
          Eq t =>
          Quadrant t -> Quadrant t -> Quadrant t -> Quadrant t -> Quadrant t
combine (Leaf va) (Leaf vb) (Leaf vc) (Leaf vd)
  = ifc_then_else_ (not (va == vb && vb == vc && vc == vd))
      (Node (Leaf va) (Leaf vb) (Leaf vc) (Leaf vd))
      (Leaf va)
combine a b c d = Node a b c d

lensWrappedTree :: Eq t => CLens (QuadTree t) (Quadrant t)
lensWrappedTree fun (Wrapper qd (w, h))
  = fmap (\ qd -> Wrapper qd (w, h)) (fun qd)

lensLeaf :: Eq t => CLens (Quadrant t) t
lensLeaf f (Leaf v) = fmap Leaf (f v)
lensLeaf f (Node a b c d) = impossible

lensA :: Eq t => CLens (Quadrant t) (Quadrant t)
lensA f (Leaf v)
  = fmap (\ x -> combine x (Leaf v) (Leaf v) (Leaf v)) (f (Leaf v))
lensA f (Node a b c d) = fmap (\ x -> combine x b c d) (f a)

lensB :: Eq t => CLens (Quadrant t) (Quadrant t)
lensB f (Leaf v)
  = fmap (\ x -> combine (Leaf v) x (Leaf v) (Leaf v)) (f (Leaf v))
lensB f (Node a b c d) = fmap (\ x -> combine a x c d) (f b)

lensC :: Eq t => CLens (Quadrant t) (Quadrant t)
lensC f (Leaf v)
  = fmap (\ x -> combine (Leaf v) (Leaf v) x (Leaf v)) (f (Leaf v))
lensC f (Node a b c d) = fmap (\ x -> combine a b x d) (f c)

lensD :: Eq t => CLens (Quadrant t) (Quadrant t)
lensD f (Leaf v)
  = fmap (combine (Leaf v) (Leaf v) (Leaf v)) (f (Leaf v))
lensD f (Node a b c d) = fmap (combine a b c) (f d)

go :: Eq t => (Nat, Nat) -> Nat -> CLens (Quadrant t) t
go _ Z = lensLeaf
go (x, y) (S deps)
  = ifc_then_else_ (y < mid)
      (ifc_then_else_ (x < mid) (lensA . go (x, y) deps)
         (lensB . go (x - mid, y) deps))
      (ifc_then_else_ (x < mid) (lensC . go (x, y - mid) deps)
         (lensD . go (x - mid, y - mid) deps))
  where
    mid :: Nat
    mid = pow 2 deps

makeTree :: Eq t => (Nat, Nat) -> t -> QuadTree t
makeTree (w, h) v = Wrapper (Leaf v) (w, h)

atLocation :: Eq t => (Nat, Nat) -> CLens (QuadTree t) t
atLocation index f qt
  = (lensWrappedTree . go index (maxDepth qt)) f qt

getLocation :: Eq t => (Nat, Nat) -> QuadTree t -> t
getLocation index = view (atLocation index)

setLocation :: Eq t => (Nat, Nat) -> t -> QuadTree t -> QuadTree t
setLocation index = set (atLocation index)

mapLocation ::
              Eq t => (Nat, Nat) -> (t -> t) -> QuadTree t -> QuadTree t
mapLocation index = over (atLocation index)

