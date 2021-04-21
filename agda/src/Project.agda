module Project where

open import Haskell.Prelude
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Relation.Nullary.Decidable using (False)

---- Useful functions

infix -2 ifc_then_else_
ifc_then_else_ : {a : Set} → (c : Bool) → ({{IsTrue c}} → a) → ({{IsFalse c}} → a) → a
ifc false then x else y = y {{IsFalse.itsFalse}}
ifc true then x else y = x {{IsTrue.itsTrue}}
{-# COMPILE AGDA2HS ifc_then_else_ #-}

infix -2 matchnat_ifzero_ifsuc_
matchnat_ifzero_ifsuc_ : (x : Nat) -> ({{IsTrue (x == 0)}} -> a) -> ({{IsFalse (x == 0)}} -> a) -> a
matchnat_ifzero_ifsuc_ x t f = ifc (x == 0)
  then (λ {{p}} -> t)
  else (λ {{p}} -> f)
{-# COMPILE AGDA2HS matchnat_ifzero_ifsuc_ #-}

div : Nat -> (divisor : Nat) -> {≢0 : False (divisor ≟ 0)} -> Nat
div a b {p} = _/_ a b {p}
-- Does not need compile, since it is already defined in haskell

_^_ : Nat -> Nat -> Nat
_^_ b zero = 1
_^_ b (suc e) = b * (b ^ e)
-- Does not need compile, since it is already defined in haskell

{-# TERMINATING #-}
log2up : Nat -> Nat
-- UNSAFE: This terminates since x/2 always decreases if x > 1
log2up x = if x <= 1 then 0 else 1 + log2up (div x 2)
{-# COMPILE AGDA2HS log2up #-}

---- Quadrants

data Quadrant (a : Set) : Set where
  Leaf : a -> Quadrant a
  Node : Quadrant a -> Quadrant a -> Quadrant a -> Quadrant a -> Quadrant a
{-# COMPILE AGDA2HS Quadrant deriving (Show, Read, Eq) #-}

instance
  quadrantFunctor : Functor Quadrant
  quadrantFunctor .fmap fn (Leaf x) = Leaf (fn x) 
  quadrantFunctor .fmap fn (Node a b c d) = Node (fmap fn a) (fmap fn b) (fmap fn c) (fmap fn d)
{-# COMPILE AGDA2HS quadrantFunctor #-}

---- Functions for quadrant

fuse : {a : Set} -> {{eqA : Eq a}} 
        -> Quadrant a -> Quadrant a
fuse old@(Node (Leaf a) (Leaf b) (Leaf c) (Leaf d)) = if a == b && b == c && c == d then Leaf a else old
fuse old = old
{-# COMPILE AGDA2HS fuse #-}

depth : {a : Set} -> {{eqA : Eq a}} -> Quadrant a -> Nat
depth (Leaf x) = 0
depth (Node a b c d) = 1 + max (max (depth a) (depth b)) (max(depth c) (depth d))
{-# COMPILE AGDA2HS depth #-}

---- QuadTree

data QuadTree (a : Set) : Set where
  -- wrappedTree, treeLength, treeWidth, treeDepth
  Wrapper : Quadrant a -> Nat -> Nat -> Nat -> QuadTree a
{-# COMPILE AGDA2HS QuadTree #-}

instance
  quadTreeFunctor : Functor QuadTree
  quadTreeFunctor .fmap fn (Wrapper q l w d) = Wrapper (fmap fn q) l w d
{-# COMPILE AGDA2HS quadTreeFunctor #-}

---- Lenses

-- Eq a => combiner function -> CLens (Quadrant a) (Quadrant a)
lensABCD : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} 
         -> ((Quadrant a) -> (Quadrant a) -> (Quadrant a) -> (Quadrant a) -> (Quadrant a) -> (Quadrant a))
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensABCD combine f (Node a b c d) = fmap (λ x -> fuse $ (combine a b c d x)) (f a)
lensABCD combine f l = fmap (λ x -> fuse $ (combine l l l l x)) (f l) where
{-# COMPILE AGDA2HS lensABCD #-}

-- Eq a => CLens (Quadrant a) (Quadrant a)
lensA : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} 
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensA = lensABCD (λ a b c d x -> Node x b c d)
{-# COMPILE AGDA2HS lensA #-}

-- Eq a => CLens (Quadrant a) (Quadrant a)
lensB : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} 
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensB = lensABCD (λ a b c d x -> Node a x c d)
{-# COMPILE AGDA2HS lensB #-}

-- Eq a => CLens (Quadrant a) (Quadrant a)
lensC : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} 
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensC = lensABCD (λ a b c d x -> Node a b x d)
{-# COMPILE AGDA2HS lensC #-}

-- Eq a => CLens (Quadrant a) (Quadrant a)
lensD : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} 
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensD = lensABCD (λ a b c d x -> Node a b c x)
{-# COMPILE AGDA2HS lensD #-}

lensWrappedTree : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} 
        -> ((Quadrant a) -> f (Quadrant a)) -> QuadTree a -> f (QuadTree a)
lensWrappedTree f (Wrapper quad l w d) = fmap (λ q -> (Wrapper q l w d)) (f quad)        
{-# COMPILE AGDA2HS lensWrappedTree #-}

---- Data access

proof_not_zero_implies_lt_one : (x : Nat) -> IsFalse (x == 0) -> IsFalse (x < 1)
proof_not_zero_implies_lt_one zero notzero = notzero
proof_not_zero_implies_lt_one (suc x) notzero = IsFalse.itsFalse

temporary_impossible : {a : Set} {{eqA : Eq a}} -> Quadrant a -> a
temporary_impossible (Leaf v) = v
temporary_impossible (Node a b c d) = temporary_impossible a
{-# COMPILE AGDA2HS temporary_impossible #-}

-- Eq a => (Nat, Nat) -> CLens (QuadTree a) a
{-# TERMINATING #-}
atLocation : {a : Set} {{eqA : Eq a}}
  -> {f : Set -> Set} {{fFunctor : Functor f}} 
  -> (Nat × Nat)
  -> (a -> f a) -> (QuadTree a) -> f (QuadTree a)
atLocation index fn qt@(Wrapper qd l w d) = (lensWrappedTree ∘ (go index d)) fn qt
  where
    -- Eq a => (Nat, Nat) -> Nat -> CLens (QuadTree a) a
    go : {a : Set} {{eqA : Eq a}}
      -> {f : Set -> Set} {{fFunctor : Functor f}} 
      -> (Nat × Nat) -> Nat
      -> (a -> f a) -> (Quadrant a) -> f (Quadrant a)
    go (x , y) d = matchnat d
      ifzero ( λ {{p}} -> 
        λ f node -> case node of 
          λ { (Leaf v) -> Leaf <$> f v 
            ; (Node a b c d) -> Leaf <$> f (temporary_impossible a) -- Impossible
            }
      )
      ifsuc ( λ {{p}} -> 
        let
          hn : Nat
          hn = _-_ d 1 {{proof_not_zero_implies_lt_one d p}}
          mid : Nat
          mid = 2 ^ hn 
        in
          ifc y < mid then
            ifc x < mid then         lensA ∘ (go (x , y) hn)
            else (λ {{x_gt_mid}} ->  lensB ∘ (go (_-_ x mid {{x_gt_mid}} , y) hn)   )
          else (λ {{y_gt_mid}} -> 
            ifc x < mid then         lensC ∘ (go (x , _-_ y mid {{y_gt_mid}}) hn)
            else (λ {{x_gt_mid}} ->  lensD ∘ (go (_-_ x mid {{x_gt_mid}} , _-_ y mid {{y_gt_mid}}) hn)   )
          )
      )
{-# COMPILE AGDA2HS atLocation #-}

data Const (a : Set) (b : Set) : Set where
  CConst : a -> Const a b

getConst : {a : Set} {b : Set} -> Const a b -> a
getConst (CConst a) = a

instance
  constFunctor : {a : Set} -> Functor (Const a)
  constFunctor .fmap f (CConst v) = CConst v

{-# COMPILE AGDA2HS Const #-}
{-# COMPILE AGDA2HS getConst #-}
{-# COMPILE AGDA2HS constFunctor #-}

data Identity (a : Set) : Set where
  CIdentity : a -> Identity a

runIdentity : {a : Set} -> Identity a -> a
runIdentity (CIdentity a) = a

instance
  identityFunctor : Functor Identity
  identityFunctor .fmap f (CIdentity v) = CIdentity (f v)

{-# COMPILE AGDA2HS Identity #-}
{-# COMPILE AGDA2HS runIdentity #-}
{-# COMPILE AGDA2HS identityFunctor #-}

getLocation : {a : Set} {{eqA : Eq a}}
  -> (Nat × Nat) -> QuadTree a -> a
getLocation {a} index qt = getConst (atLocation index CConst qt)
{-# COMPILE AGDA2HS getLocation #-}

setLocation : {a : Set} {{eqA : Eq a}}
  -> (Nat × Nat) -> a -> QuadTree a -> QuadTree a
setLocation index v qt = runIdentity (atLocation index (λ _ -> CIdentity v) qt)
{-# COMPILE AGDA2HS setLocation #-}

mapLocation : {a : Set} {{eqA : Eq a}}
  -> (Nat × Nat) -> (a -> a) -> QuadTree a -> QuadTree a
mapLocation index f qt = runIdentity (atLocation index (CIdentity ∘ f) qt)
{-# COMPILE AGDA2HS mapLocation #-}

makeTree : {a : Set} {{eqA : Eq a}} -> (Nat × Nat) -> a -> QuadTree a
makeTree (w , h) a = Wrapper (Leaf a) w h (log2up (max w h) ) 
{-# COMPILE AGDA2HS makeTree #-}

-- x = makeTree (4 , 4) 'x'
-- y = getLocation (2 , 2) x
