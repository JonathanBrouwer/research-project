module Data.QuadTree.InternalAgda where

import Numeric.Natural (Natural)

ifc_then_else_ :: Bool -> a -> a -> a
ifc_then_else_ False x₁ y = y
ifc_then_else_ True x₁ y = x₁

matchnat_ifzero_ifsuc_ :: Natural -> a -> a -> a
matchnat_ifzero_ifsuc_ x₁ t f = ifc_then_else_ (x₁ == 0) t f

pow :: Natural -> Natural -> Natural
pow b e = ifc_then_else_ (e == 0) 1 (b * pow b (e - 1))

log2up :: Natural -> Natural
log2up x₁ = if x₁ <= 1 then 0 else 1 + log2up (div x₁ 2)

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

data Quadrant a = Leaf a
                | Node (Quadrant a) (Quadrant a) (Quadrant a) (Quadrant a)
                    deriving (Show, Read, Eq)

instance Functor Quadrant where
    fmap fn (Leaf x₁) = Leaf (fn x₁)
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

makeTree :: Eq a => (Natural, Natural) -> a -> QuadTree a
makeTree (w, h) a = Wrapper (Leaf a) w h (log2up (max w h))

depth :: Quadrant a -> Natural
depth (Leaf x₁) = 0
depth (Node a b c d)
  = 1 + max (max (depth a) (depth b)) (max (depth c) (depth d))

checkValid :: Eq a => QuadTree a -> Bool
checkValid (Wrapper qd _ _ d) = d >= depth qd

lensA ::
        Eq a =>
          Functor f =>
          (Quadrant a -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensA f (Node a b c d) = fmap (\ x -> fuse (Node x b c d)) (f a)
lensA f l = fmap (\ x -> fuse $ Node x l l l) (f l)

lensB ::
        Eq a =>
          Functor f =>
          (Quadrant a -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensB f (Node a b c d) = fmap (\ x -> fuse (Node a x c d)) (f b)
lensB f l = fmap (\ x -> fuse $ Node l x l l) (f l)

lensC ::
        Eq a =>
          Functor f =>
          (Quadrant a -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensC f (Node a b c d) = fmap (\ x -> fuse (Node a b x d)) (f c)
lensC f l = fmap (\ x -> fuse $ Node l l x l) (f l)

lensD ::
        Eq a =>
          Functor f =>
          (Quadrant a -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensD f (Node a b c d) = fmap (\ x -> fuse (Node a b c x)) (f d)
lensD f l = fmap (\ x -> fuse $ Node l l l x) (f l)

lensWrappedTree ::
                  Functor f =>
                  (Quadrant a -> f (Quadrant a)) -> QuadTree a -> f (QuadTree a)
lensWrappedTree f (Wrapper quad l w d)
  = fmap (\ q -> Wrapper q l w d) (f quad)

readLeaf :: Eq t => Quadrant t -> t
readLeaf (Leaf v) = v
readLeaf (Node a b c d) = error "readLeaf: impossible"

af :: Bool -> (Bool, Bool)
af y = (y, y)

data Test = TestC Bool

x :: Test
x = TestC True

