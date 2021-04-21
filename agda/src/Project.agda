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
lens_abcd : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} 
         -> ((Quadrant a) -> (Quadrant a) -> (Quadrant a) -> (Quadrant a) -> (Quadrant a) -> (Quadrant a))
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lens_abcd combine f (Node a b c d) = fmap (λ x -> fuse $ (combine a b c d x)) (f a)
lens_abcd combine f l = fmap (λ x -> fuse $ (combine l l l l x)) (f l) where
{-# COMPILE AGDA2HS lens_abcd #-}

-- Eq a => CLens (Quadrant a) (Quadrant a)
lens_a : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} 
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lens_a = lens_abcd (λ a b c d x -> Node x b c d)
{-# COMPILE AGDA2HS lens_a #-}

-- Eq a => CLens (Quadrant a) (Quadrant a)
lens_b : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} 
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lens_b = lens_abcd (λ a b c d x -> Node a x c d)
{-# COMPILE AGDA2HS lens_b #-}

-- Eq a => CLens (Quadrant a) (Quadrant a)
lens_c : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} 
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lens_c = lens_abcd (λ a b c d x -> Node a b x d)
{-# COMPILE AGDA2HS lens_c #-}

-- Eq a => CLens (Quadrant a) (Quadrant a)
lens_d : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} 
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lens_d = lens_abcd (λ a b c d x -> Node a b c x)
{-# COMPILE AGDA2HS lens_d #-}

lens_wrappedtree : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} 
        -> ((Quadrant a) -> f (Quadrant a)) -> QuadTree a -> f (QuadTree a)
lens_wrappedtree f (Wrapper quad l w d) = fmap (λ q -> (Wrapper q l w d)) (f quad)        
{-# COMPILE AGDA2HS lens_wrappedtree #-}

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
atLocation index fn qt@(Wrapper qd l w d) = (lens_wrappedtree ∘ (go index d)) fn qt
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
        lens_a ∘ go (x , y) (_-_ d 1 {{proof_not_zero_implies_lt_one d p}}) )
{-# COMPILE AGDA2HS atLocation #-}

-- Eq a => (Nat, Nat) -> QuadTree a -> a -> a
-- getLocation : {a : Set} {{eqA : Eq a}} -> (Nat × Nat) -> QuadTree a -> a
-- getLocation (x , y) (Wrapper quad l w d) = go (x , y) d quad 
--   where
--     go : {a : Set} {{eqA : Eq a}} -> (Nat × Nat) -> Nat -> Quadrant a -> a
--     go (x , y) 0 (Leaf v) = v
--     go (x , y) _ (Leaf v) = v
--     go (x , y) depth (Node a b c d) = matchnat depth
--       ifzero 
--         temporary_impossible a
--       ifsuc 
--         ifc y < mid then
--           ifc x < mid then         go (x , y) hn a
--           else (λ {{x_gt_mid}} ->  go (_-_ x mid {{x_gt_mid}} , y) hn b )
--         else (λ {{y_gt_mid}} -> 
--           ifc x < mid then         go (x , _-_ y mid {{y_gt_mid}}) hn c
--           else (λ {{x_gt_mid}} ->  go (_-_ x mid {{x_gt_mid}} , _-_ y mid {{y_gt_mid}}) hn d ))
--       where
--         temporary_impossible : {a : Set} {{eqA : Eq a}} -> Quadrant a -> a
--         temporary_impossible (Leaf v) = v
--         temporary_impossible (Node a b c d) = temporary_impossible a
--         hn : Nat
--         hn = ifc depth < 1 then 0 else depth - 1 -- depth < 1 is IMPOSSIBLE
--         mid : Nat
--         mid = 2 ^ hn   
-- {-# COMPILE AGDA2HS getLocation #-}

makeTree : {a : Set} {{eqA : Eq a}} -> (Nat × Nat) -> a -> QuadTree a
makeTree (w , h) a = Wrapper (Leaf a) w h (log2up (max w h) ) 
{-# COMPILE AGDA2HS makeTree #-}

-- x = makeTree (4 , 4) 'x'
-- y = getLocation (2 , 2) x
