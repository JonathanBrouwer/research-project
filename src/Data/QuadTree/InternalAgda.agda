module Data.QuadTree.InternalAgda where

open import Haskell.Prelude
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Relation.Nullary.Decidable using (False)

---- General purpose proofs

propNotZeroImpliesLtOne : (x : Nat) -> IsFalse (x == 0) -> IsFalse (x < 1)
propNotZeroImpliesLtOne zero notzero = notzero
propNotZeroImpliesLtOne (suc x) notzero = IsFalse.itsFalse

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

{-# TERMINATING #-}
-- UNSAFE: This terminates e always decreases
pow : Nat -> Nat -> Nat
pow b e = ifc e == 0 then 1 else (λ {{p}} -> b * pow b (_-_ e 1 {{propNotZeroImpliesLtOne e p}}))
{-# COMPILE AGDA2HS pow #-}

{-# TERMINATING #-}
log2up : Nat -> Nat
-- UNSAFE: This terminates since x/2 always decreases if x > 1
log2up x = if x <= 1 then 0 else 1 + log2up (div x 2)
{-# COMPILE AGDA2HS log2up #-}

---- Functors

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

---- QuadTree

data QuadTree (a : Set) : Set where
  -- wrappedTree, treeLength, treeWidth, treeDepth
  Wrapper : Quadrant a -> Nat -> Nat -> Nat -> QuadTree a
{-# COMPILE AGDA2HS QuadTree deriving (Show, Read, Eq) #-}

instance
  quadTreeFunctor : Functor QuadTree
  quadTreeFunctor .fmap fn (Wrapper q l w d) = Wrapper (fmap fn q) l w d
{-# COMPILE AGDA2HS quadTreeFunctor #-}

makeTree : {a : Set} {{eqA : Eq a}} -> (Nat × Nat) -> a -> QuadTree a
makeTree (w , h) a = Wrapper (Leaf a) w h (log2up (max w h) )
{-# COMPILE AGDA2HS makeTree #-}


---- Check if valid

depth : {a : Set} -> Quadrant a -> Nat
depth (Leaf x) = 0
depth (Node a b c d) = 1 + max (max (depth a) (depth b)) (max(depth c) (depth d))
{-# COMPILE AGDA2HS depth #-}

checkValid : {a : Set} {{eqA : Eq a}} -> QuadTree a -> Bool
checkValid (Wrapper qd _ _ d) = d >= depth qd
{-# COMPILE AGDA2HS checkValid #-}

data IsValid : {a : Set} {{eqA : Eq a}} -> QuadTree a -> Set where
  valid : {a} -> {{eqA : Eq a}} -> (qt : QuadTree a) -> IsTrue (checkValid qt) -> IsValid qt

data MaxDepth : {a : Set} -> Quadrant a -> Nat -> Set where
  maxDepth : (qd : Quadrant a) -> (d : Nat) -> IsTrue ((depth qd) <= d) -> MaxDepth qd d 

---- Properties of depth

useEq : {x y : Bool} -> x ≡ y -> IsTrue x -> IsTrue y
useEq {true} {true} eq is = IsTrue.itsTrue

-- symmetry of equality
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- transitivity of equality
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

-- congruence of equality
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
begin p = p

_end : {A : Set} → (x : A) → x ≡ x
x end = refl

_=⟨_⟩_ : {A : Set} → (x : A) → {y z : A}
       → x ≡ y → y ≡ z → x ≡ z
x =⟨ p ⟩ q = trans p q

_=⟨⟩_ : {A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
x =⟨⟩ q = x =⟨ refl ⟩ q

infix   1  begin_
infix   3  _end
infixr  2  _=⟨_⟩_
infixr  2  _=⟨⟩_

propFnIf : {a b : Set} -> (c : Bool) (x : a) (y : a) (f : a -> b) -> (if c then f x else f y) ≡ f (if c then x else y)
propFnIf false x y f = refl
propFnIf true x y f = refl

propMaxSuc : (x y : Nat) -> max (suc x) (suc y) ≡ suc (max x y)
propMaxSuc zero zero = refl
propMaxSuc zero (suc y) = refl
propMaxSuc (suc x) zero = refl
propMaxSuc (suc x) (suc y) =
  begin
    max (suc $ suc x) (suc $ suc y)
  =⟨⟩
    (if x < y then (suc $ suc y) else (suc $ suc x))
  =⟨ propFnIf (x < y) (suc y) (suc x) suc ⟩
    (suc $ (if x < y then (suc y) else (suc x)))
  =⟨⟩
    suc (max (suc x) (suc y))
  end

propMaxRefl : (x y : Nat) -> max x y ≡ max y x
propMaxRefl zero zero = refl
propMaxRefl zero (suc y) = refl
propMaxRefl (suc x) zero = refl
propMaxRefl (suc x) (suc y) =
  begin
    max (suc x) (suc y)
  =⟨ propMaxSuc x y ⟩
    suc (max x y)
  =⟨ cong suc (propMaxRefl x y) ⟩
    suc (max y x)
  =⟨ sym $ propMaxSuc y x ⟩
    max (suc y) (suc x)
  end

propIsTrueCombine2 : {a b : Bool} -> IsTrue a -> IsTrue b -> IsTrue (a && b)
propIsTrueCombine2 {true} {true} ta tb = IsTrue.itsTrue

propIsTrueCombine4 : {a b c d : Bool} -> IsTrue a -> IsTrue b -> IsTrue c -> IsTrue d -> IsTrue ((a && b) && (c && d))
propIsTrueCombine4 {true} {true} {true} {true} ta tb tc td = IsTrue.itsTrue

andRefl : (a b : Bool) -> (a && b) ≡ (b && a)
andRefl false false = refl
andRefl false true = refl
andRefl true false = refl
andRefl true true = refl

boolAndTrue : (a : Bool) -> (a && true) ≡ a
boolAndTrue false = refl
boolAndTrue true = refl

lteTransitiveWeird : (x y d : Nat) -> IsTrue (x < y) -> (y <= d) ≡ ((x <= d) && (y <= d))
lteTransitiveWeird zero zero zero xlty = refl
lteTransitiveWeird zero zero (suc d) xlty = refl
lteTransitiveWeird zero (suc y) zero xlty = refl
lteTransitiveWeird zero (suc y) (suc d) xlty = refl
lteTransitiveWeird (suc x) (suc y) zero xlty = refl
lteTransitiveWeird (suc x) (suc y) (suc d) xlty = lteTransitiveWeird x y d xlty

lteTransitiveWeirdInv : (x y d : Nat) -> IsFalse (x < y) -> (x <= d) ≡ ((x <= d) && (y <= d))
lteTransitiveWeirdInv zero zero zero xnlty = refl
lteTransitiveWeirdInv zero zero (suc d) xnlty = refl
lteTransitiveWeirdInv (suc x) zero zero xnlty = refl
lteTransitiveWeirdInv (suc x) zero (suc d) xnlty =
  begin
    (suc x <= suc d)
  =⟨ sym $ boolAndTrue (suc x <= suc d) ⟩
    (suc x <= suc d) && true
  =⟨⟩
    ((suc x <= suc d) && (zero <= suc d))
  end
lteTransitiveWeirdInv (suc x) (suc y) zero xnlty = refl
lteTransitiveWeirdInv (suc x) (suc y) (suc d) xnlty = lteTransitiveWeirdInv x y d xnlty

ifTrue : (a b c : Bool) -> IsTrue c -> (if c then a else b) ≡ a
ifTrue a b true tc = refl

ifFalse : (a b c : Bool) -> IsFalse c -> (if c then a else b) ≡ b
ifFalse a b false fc = refl

ifComparisonMap : (x y d : Nat) -> ((x <= d) && (y <= d)) ≡ (if x < y then (y <= d) else (x <= d))
ifComparisonMap x y d = ifc x < y 
  then (λ {{xlty}} ->
    begin
      (x <= d) && (y <= d)
    =⟨ sym $ lteTransitiveWeird x y d xlty ⟩
      y <= d
    =⟨ sym $ ifTrue (y <= d) (x <= d) (x < y) xlty ⟩
      (if x < y then (y <= d) else (x <= d))
    end
  )
  else (λ {{xnlty}} ->
    begin
      (x <= d) && (y <= d)
    =⟨ sym $ lteTransitiveWeirdInv x y d xnlty ⟩
      x <= d
    =⟨ sym $ ifFalse (y <= d) (x <= d) (x < y) xnlty ⟩
      (if x < y then (y <= d) else (x <= d))
    end
  )

propMaxLte : (x y d : Nat) -> ((x <= d) && (y <= d)) ≡ (max x y <= d)
propMaxLte x y d = 
  begin
    (x <= d) && (y <= d)
  =⟨ ifComparisonMap x y d ⟩
    (if x < y then (y <= d) else (x <= d))
  =⟨ propFnIf (x < y) y x (λ v -> v <= d) ⟩
    (if x < y then y else x) <= d
  =⟨⟩
    max x y <= d
  end

propAndMap : (a b c d : Bool) -> a ≡ c -> b ≡ d -> (a && b) ≡ (c && d)
propAndMap false false false false ac bd = refl
propAndMap false true false true ac bd = refl
propAndMap true false true false ac bd = refl
propAndMap true true true true ac bd = refl

propMaxLte4 : (w x y z d : Nat) -> (((w <= d) && (x <= d)) && ((y <= d) && (z <= d))) ≡ (max (max w x) (max y z) <= d)
propMaxLte4 w x y z d =
  begin
    ((w <= d) && (x <= d)) && ((y <= d) && (z <= d))
  =⟨ propAndMap ((w <= d) && (x <= d)) ((y <= d) && (z <= d)) (max w x <= d) (max y z <= d) (propMaxLte w x d) (propMaxLte y z d) ⟩
    (max w x <= d) && (max y z <= d)
  =⟨ propMaxLte (if w < x then x else w) (if y < z then z else y) d ⟩
    (max (max w x) (max y z) <= d)
  end

propDepthRelationEq : {t : Set} -> (a b c d : Quadrant t) -> depth (Node a b c d) ≡ (1 + (max (max (depth a) (depth b)) (max (depth c) (depth d))))
propDepthRelationEq a b c d = refl

propDepthRelationLte : {t : Set} -> (a b c d : Quadrant t) -> (dep : Nat) 
  -> ((depth a <= dep && depth b <= dep) && (depth c <= dep && depth d <= dep)) ≡ (depth (Node a b c d) <= (suc dep))
propDepthRelationLte a b c d dep =
  begin 
    ((depth a <= dep && depth b <= dep) && (depth c <= dep && depth d <= dep))
  =⟨ propMaxLte4 (depth a) (depth b) (depth c) (depth d) dep ⟩
    (max (max (depth a) (depth b)) (max (depth c) (depth d)) <= dep)
  =⟨⟩
    (depth (Node a b c d) <= suc dep)
  end

---- Lenses

-- Eq a => CLens (Quadrant a) (Quadrant a)
lensA : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}}
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensA f (Node a b c d) = fmap (λ x -> fuse ( Node x b c d)) (f a)
lensA f l = fmap ((λ x -> fuse $ Node x l l l)) (f l)
{-# COMPILE AGDA2HS lensA #-}

-- Can we define a type with an implicit argument, and define a different haskell type??6
-- propLensA : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} ->
--   (qd : Quadrant a) -> lensA f qd ≡ lensA f qd
-- propLensA = {!   !}

-- Eq a => CLens (Quadrant a) (Quadrant a)
lensB : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}}
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensB f (Node a b c d) = fmap (λ x -> fuse ( Node a x c d)) (f b)
lensB f l = fmap ((λ x -> fuse $  Node l x l l)) (f l)
{-# COMPILE AGDA2HS lensB #-}

-- Eq a => CLens (Quadrant a) (Quadrant a)
lensC : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}}
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensC f (Node a b c d) = fmap (λ x -> fuse ( Node a b x d)) (f c)
lensC f l = fmap ((λ x -> fuse $  Node l l x l)) (f l)
{-# COMPILE AGDA2HS lensC #-}

-- Eq a => CLens (Quadrant a) (Quadrant a)
lensD : {a : Set} {{eqA : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}}
         -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
lensD f (Node a b c d) = fmap (λ x -> fuse ( Node a b c x)) (f d)
lensD f l = fmap ((λ x -> fuse $ Node l l l x)) (f l)
{-# COMPILE AGDA2HS lensD #-}

lensWrappedTree : {a : Set} {f : Set -> Set} {{fFunctor : Functor f}}
        -> ((Quadrant a) -> f (Quadrant a)) -> QuadTree a -> f (QuadTree a)
lensWrappedTree f (Wrapper quad l w d) = fmap (λ q -> (Wrapper q l w d)) (f quad)
{-# COMPILE AGDA2HS lensWrappedTree #-}

---- Data access

bottom = ⊥

readLeaf : {t : Set} {{eqA : Eq t}} -> (qd : Quadrant t) -> {MaxDepth qd 0} -> t
readLeaf (Leaf v) {md} = v
readLeaf (Node a b c d) {maxDepth .(Node a b c d) .0 ()}
{-# COMPILE AGDA2HS readLeaf #-}

transformMaxDepth : {t : Set} {{eqA : Eq t}} -> (qd : Quadrant t) -> (d : Nat) -> {MaxDepth qd d} -> {IsTrue (d == 0)} -> MaxDepth qd 0
transformMaxDepth qd zero {maxDepth .qd .0 x} {d0} = maxDepth qd 0 x

af : Bool -> {Bool} -> (Bool × Bool)
af y = (y , y)

{-# COMPILE AGDA2HS af #-}
-- -- Eq a => (Nat, Nat) -> Nat -> CLens (QuadTree a) a
-- {-# TERMINATING #-}
-- go : {a : Set} {{eqA : Eq a}}
--   -> {f : Set -> Set} {{fFunctor : Functor f}}
--   -> (Nat × Nat) -> (d : Nat)
--   -> (a -> f a) -> (qd : Quadrant a) -> {MaxDepth qd d} -> f (Quadrant a)
-- go (x , y) d = matchnat d
--   ifzero ( λ {{p}} ->
--     -- Uses readLeaf and transformMaxDepth to proof that qd must be a Leaf, and not a Node
--     λ f qd {md} -> Leaf <$> (f $ readLeaf qd { transformMaxDepth qd d {md} {p} })
--   )
--   ifsuc ( λ {{p}} ->
--     let
--       -- Subtract one from d (d sub), using the fact that d > 0 from ifsuc
--       ds = _-_ d 1 {{propNotZeroImpliesLtOne d p}}
--       mid = pow 2 ds
--     in
--       {!   !}
--     --   ifc y < mid then
--     --     ifc x < mid then         lensA ∘ (go (x , y) ds)
--     --     else (λ {{x_gt_mid}} ->  lensB ∘ (go (_-_ x mid {{x_gt_mid}} , y) ds)   )
--     --   else (λ {{y_gt_mid}} ->
--     --     ifc x < mid then         lensC ∘ (go (x , _-_ y mid {{y_gt_mid}}) ds)
--     --     else (λ {{x_gt_mid}} ->  lensD ∘ (go (_-_ x mid {{x_gt_mid}} , _-_ y mid {{y_gt_mid}}) ds)   )
--     --   ) 
--   )
-- {-# COMPILE AGDA2HS go #-}

-- Eq a => (Nat, Nat) -> CLens (QuadTree a) a
-- atLocation : {a : Set} {{eqA : Eq a}}
--   -> {f : Set -> Set} {{fFunctor : Functor f}}
--   -> (Nat × Nat)
--   -> (a -> f a) -> (qt : QuadTree a) -> {{IsValid qt}} -> f (QuadTree a)
-- atLocation index fn qt@(Wrapper qd l w d) ⦃ valid .(Wrapper qd l w d) x ⦄ = (lensWrappedTree ∘ (go index d)) fn {!  !}
-- {-# COMPILE AGDA2HS atLocation #-}

---- Functions using functors

-- getLocation : {a : Set} {{eqA : Eq a}}
--   -> (Nat × Nat) -> QuadTree a -> a
-- getLocation index qt = getConst (atLocation index CConst qt)
-- {-# COMPILE AGDA2HS getLocation #-}

-- setLocation : {a : Set} {{eqA : Eq a}}
--   -> (Nat × Nat) -> a -> QuadTree a -> QuadTree a
-- setLocation index v qt = runIdentity (atLocation index (λ _ -> CIdentity v) qt)
-- {-# COMPILE AGDA2HS setLocation #-}

-- mapLocation : {a : Set} {{eqA : Eq a}}
--   -> (Nat × Nat) -> (a -> a) -> QuadTree a -> QuadTree a
-- mapLocation index f qt = runIdentity (atLocation index (CIdentity ∘ f) qt)
-- {-# COMPILE AGDA2HS mapLocation #-}

