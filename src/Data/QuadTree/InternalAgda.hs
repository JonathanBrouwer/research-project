module Data.QuadTree.InternalAgda where

import Numeric.Natural (Natural)

ifc_then_else_ :: Bool -> a -> a -> a
ifc_then_else_ False x y = y
ifc_then_else_ True x y = x

matchnat_ifzero_ifsuc_ :: Natural -> a -> a -> a
matchnat_ifzero_ifsuc_ x t f = ifc_then_else_ (x == 0) t f

pow :: Natural -> Natural -> Natural
pow b e = ifc_then_else_ (e == 0) 1 (b * pow b (e - 1))

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

data QuadTree a = Wrapper (Quadrant a) Natural Natural Natural
                    deriving (Show, Read, Eq)

instance Functor QuadTree where
    fmap fn (Wrapper q l w d) = Wrapper (fmap fn q) l w d

depth :: Eq a => Quadrant a -> Natural
depth (Leaf x) = 0
depth (Node a b c d)
  = 1 + max (max (depth a) (depth b)) (max (depth c) (depth d))

checkValid :: Eq a => QuadTree a -> Bool
checkValid (Wrapper qd _ _ d) = d >= depth qd

lensABCD ::
           Eq a =>
             Functor f =>
             (Quadrant a ->
                Quadrant a -> Quadrant a -> Quadrant a -> Quadrant a -> Quadrant a)
               ->
               (Quadrant a ->
                  Quadrant a -> Quadrant a -> Quadrant a -> Quadrant a)
                 -> (Quadrant a -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensABCD combine select f (Node a b c d)
  = fmap (fuse . combine a b c d) (f (select a b c d))
lensABCD combine select f l = fmap (fuse . combine l l l l) (f l)

lensA ::
        Eq a =>
          Functor f =>
          (Quadrant a -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensA = lensABCD (\ a b c d x -> Node x b c d) (\ a b c d -> a)

lensB ::
        Eq a =>
          Functor f =>
          (Quadrant a -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensB = lensABCD (\ a b c d x -> Node a x c d) (\ a b c d -> b)

lensC ::
        Eq a =>
          Functor f =>
          (Quadrant a -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensC = lensABCD (\ a b c d x -> Node a b x d) (\ a b c d -> c)

lensD ::
        Eq a =>
          Functor f =>
          (Quadrant a -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensD = lensABCD (\ a b c d x -> Node a b c x) (\ a b c d -> d)

lensWrappedTree ::
                  Functor f =>
                  (Quadrant a -> f (Quadrant a)) -> QuadTree a -> f (QuadTree a)
lensWrappedTree f (Wrapper quad l w d)
  = fmap (\ q -> Wrapper q l w d) (f quad)

temporaryImpossible :: Eq a => Quadrant a -> a
temporaryImpossible (Leaf v) = v
temporaryImpossible (Node a b c d) = temporaryImpossible d

go ::
     Eq a =>
       Functor f =>
       (Natural, Natural) ->
         Natural -> (a -> f a) -> Quadrant a -> f (Quadrant a)
go (x, y) d
  = matchnat_ifzero_ifsuc_ d
      (\ f node ->
         case node of
             Leaf v -> Leaf <$> f v
             Node a b c d₁ -> Leaf <$> f (temporaryImpossible a))
      (ifc_then_else_ (y < pow 2 (d - 1))
         (ifc_then_else_ (x < pow 2 (d - 1)) (lensA . go (x, y) (d - 1))
            (lensB . go (x - pow 2 (d - 1), y) (d - 1)))
         (ifc_then_else_ (x < pow 2 (d - 1))
            (lensC . go (x, y - pow 2 (d - 1)) (d - 1))
            (lensD . go (x - pow 2 (d - 1), y - pow 2 (d - 1)) (d - 1))))

atLocation ::
             Eq a =>
               Functor f =>
               (Natural, Natural) -> (a -> f a) -> QuadTree a -> f (QuadTree a)
atLocation index fn (Wrapper qd l w d)
  = (lensWrappedTree . go index d) fn (Wrapper qd l w d)

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

