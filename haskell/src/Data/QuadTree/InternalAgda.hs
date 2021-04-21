module Data.QuadTree.InternalAgda where

import Numeric.Natural (Natural)

ifc_then_else_ :: Bool -> a -> a -> a
ifc_then_else_ False x y = y
ifc_then_else_ True x y = x

matchnat_ifzero_ifsuc_ :: Natural -> a -> a -> a
matchnat_ifzero_ifsuc_ x t f = ifc_then_else_ (x == 0) t f

log2up :: Natural -> Natural
log2up x = if x <= 1 then 0 else 1 + log2up (div x 2)

data Quadrant a = Leaf a
                | Node (Quadrant a) (Quadrant a) (Quadrant a) (Quadrant a)
                    deriving (Show, Read, Eq)

instance Functor Quadrant where
    fmap fn (Leaf x) = Leaf (fn x)
    fmap fn (Node a b c d)
      = Node (fmap fn a) (fmap fn b) (fmap fn c) (fmap fn d)

fuse :: Eq a => Quadrant a -> Quadrant a
fuse (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d))
  = if a == b && b == c && c == d then Leaf a else
      Node (Leaf a) (Leaf b) (Leaf c) (Leaf d)
fuse old = old

depth :: Eq a => Quadrant a -> Natural
depth (Leaf x) = 0
depth (Node a b c d)
  = 1 + max (max (depth a) (depth b)) (max (depth c) (depth d))

data QuadTree a = Wrapper (Quadrant a) Natural Natural Natural

instance Functor QuadTree where
    fmap fn (Wrapper q l w d) = Wrapper (fmap fn q) l w d

lensABCD ::
           Eq a =>
             Functor f =>
             (Quadrant a ->
                Quadrant a -> Quadrant a -> Quadrant a -> Quadrant a -> Quadrant a)
               -> (Quadrant a -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensABCD combine f (Node a b c d)
  = fmap (fuse . combine a b c d) (f a)
lensABCD combine f l = fmap (fuse . combine l l l l) (f l)

lensA ::
        Eq a =>
          Functor f =>
          (Quadrant a -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensA = lensABCD (\ a b c d x -> Node x b c d)

lensB ::
        Eq a =>
          Functor f =>
          (Quadrant a -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensB = lensABCD (\ a b c d x -> Node a x c d)

lensC ::
        Eq a =>
          Functor f =>
          (Quadrant a -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensC = lensABCD (\ a b c d x -> Node a b x d)

lensD ::
        Eq a =>
          Functor f =>
          (Quadrant a -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensD = lensABCD (\ a b c d x -> Node a b c x)

lensWrappedTree ::
                  Functor f =>
                  (Quadrant a -> f (Quadrant a)) -> QuadTree a -> f (QuadTree a)
lensWrappedTree f (Wrapper quad l w d)
  = fmap (\ q -> Wrapper q l w d) (f quad)

temporary_impossible :: Eq a => Quadrant a -> a
temporary_impossible (Leaf v) = v
temporary_impossible (Node a b c d) = temporary_impossible a

atLocation ::
             Eq a =>
               Functor f =>
               (Natural, Natural) -> (a -> f a) -> QuadTree a -> f (QuadTree a)
atLocation index fn (Wrapper qd l w d)
  = (lensWrappedTree . go index d) fn (Wrapper qd l w d)
  where
    go ::
         Eq a =>
           Functor f =>
           (Natural, Natural) ->
             Natural -> (a -> f a) -> Quadrant a -> f (Quadrant a)
    go (x, y) d₁
      = matchnat_ifzero_ifsuc_ d₁
          (\ f node ->
             case node of
                 Leaf v -> Leaf <$> f v
                 Node a b c d₂ -> Leaf <$> f (temporary_impossible a))
          (ifc_then_else_ (y < 2 ^ d₁ - 1)
             (ifc_then_else_ (x < 2 ^ d₁ - 1) (lensA . go (x, y) (d₁ - 1))
                (lensB . go (x - 2 ^ d₁ - 1, y) (d₁ - 1)))
             (ifc_then_else_ (x < 2 ^ d₁ - 1)
                (lensC . go (x, y - 2 ^ d₁ - 1) (d₁ - 1))
                (lensD . go (x - 2 ^ d₁ - 1, y - 2 ^ d₁ - 1) (d₁ - 1))))

data Const a b = CConst a

getConst :: Const a b -> a
getConst (CConst a) = a

instance Functor (Const a) where
    fmap f (CConst v) = CConst v

data Identity a = CIdentity a

runIdentity :: Identity a -> a
runIdentity (CIdentity a) = a

instance Functor Identity where
    fmap f (CIdentity v) = CIdentity (f v)

getLocation :: Eq a => (Natural, Natural) -> QuadTree a -> a
getLocation index qt = getConst (atLocation index CConst qt)

setLocation ::
              Eq a => (Natural, Natural) -> a -> QuadTree a -> QuadTree a
setLocation index v qt
  = runIdentity (atLocation index (\ _ -> CIdentity v) qt)

mapLocation ::
              Eq a => (Natural, Natural) -> (a -> a) -> QuadTree a -> QuadTree a
mapLocation index f qt
  = runIdentity (atLocation index (CIdentity . f) qt)

makeTree :: Eq a => (Natural, Natural) -> a -> QuadTree a
makeTree (w, h) a = Wrapper (Leaf a) w h (log2up (max w h))

