module Data.QuadTree.Logic where

open import Haskell.Prelude
open import Relation.Nullary.Decidable
open import Data.Nat.DivMod
open import Data.Nat.Properties

---- Equational reasoning
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

---- General purpose proofs

propZeroImpliesLtOne : (x : Nat) -> IsFalse (x == 0) -> IsFalse (x < 1)
propZeroImpliesLtOne zero notzero = notzero
propZeroImpliesLtOne (suc x) notzero = IsFalse.itsFalse

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

andFst : {a b : Bool} -> IsTrue (a && b) -> IsTrue a
andFst {true} {true} ab = IsTrue.itsTrue

andSnd : {a b : Bool} -> IsTrue (a && b) -> IsTrue b
andSnd {true} {true} ab = IsTrue.itsTrue

boolAndTrue : (a : Bool) -> (a && true) ≡ a
boolAndTrue false = refl
boolAndTrue true = refl

ifTrue : (a b c : Bool) -> IsTrue c -> (if c then a else b) ≡ a
ifTrue a b true tc = refl

ifFalse : (a b c : Bool) -> IsFalse c -> (if c then a else b) ≡ b
ifFalse a b false fc = refl

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

---- Useful functions

div : Nat -> (divisor : Nat) -> {≢0 : False (divisor ≟ 0)} -> Nat
div a b {p} = _/_ a b {p}
-- Does not need compile, since it is already defined in haskell

{-# TERMINATING #-}
-- UNSAFE: This terminates e always decreases
pow : Nat -> Nat -> Nat
pow b e = ifc e == 0 then 1 else (λ {{p}} -> b * pow b (_-_ e 1 {{propZeroImpliesLtOne e p}}))
{-# COMPILE AGDA2HS pow #-}

{-# TERMINATING #-}
log2up : Nat -> Nat
-- UNSAFE: This terminates since x/2 always decreases if x > 1
log2up x = if x <= 1 then 0 else 1 + log2up (div (x + 1) 2)
{-# COMPILE AGDA2HS log2up #-}


zeroLteAny : (a : Nat) -> IsTrue (0 <= a)
zeroLteAny zero = IsTrue.itsTrue
zeroLteAny (suc a) = IsTrue.itsTrue

lteTransitive : (a b c : Nat) -> IsTrue (a <= b) -> IsTrue (b <= c) -> IsTrue (a <= c)
lteTransitive zero zero c ab bc = bc
lteTransitive zero (suc b) (suc c) ab bc = IsTrue.itsTrue
lteTransitive (suc a) (suc b) (suc c) ab bc = lteTransitive a b c ab bc

incrLte : (a b : Nat) -> IsTrue (a <= b) -> IsTrue (a <= suc b)
incrLte zero zero altb = IsTrue.itsTrue
incrLte zero (suc b) altb = IsTrue.itsTrue
incrLte (suc a) (suc b) altb = incrLte a b altb

natPlusMinNat : (x : Nat) -> {{p : IsFalse (x < 1)}} -> x ≡ (suc (x - 1))
natPlusMinNat (suc x) = refl

transformLteRight : {a b c : Nat} -> b ≡ c -> IsTrue (a <= b) -> IsTrue (a <= c)
transformLteRight {a} {b} {.b} refl ab = ab

lteSelf : (v : Nat) -> IsTrue (v <= v)
lteSelf zero = IsTrue.itsTrue
lteSelf (suc v) = lteSelf v