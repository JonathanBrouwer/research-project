module Data.QuadTree.Logic where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Relation.Nullary.Decidable
open import Data.Nat.DivMod
open import Data.Nat.Properties
{-# FOREIGN AGDA2HS
import Data.Nat
#-}


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
propZeroImpliesLtOne Z notZ = notZ
propZeroImpliesLtOne (S x) notZ = IsFalse.itsFalse

propFnIf : {a b : Set} -> (c : Bool) (x : a) (y : a) (f : a -> b) -> (if c then f x else f y) ≡ f (if c then x else y)
propFnIf false x y f = refl
propFnIf true x y f = refl

propMaxSuc : (x y : Nat) -> max (S x) (S y) ≡ S (max x y)
propMaxSuc Z Z = refl
propMaxSuc Z (S y) = refl
propMaxSuc (S x) Z = refl
propMaxSuc (S x) (S y) =
  begin
    max (S $ S x) (S $ S y)
  =⟨⟩
    (if x < y then (S $ S y) else (S $ S x))
  =⟨ propFnIf (x < y) (S y) (S x) S ⟩
    (S $ (if x < y then (S y) else (S x)))
  =⟨⟩
    S (max (S x) (S y))
  end

propMaxRefl : (x y : Nat) -> max x y ≡ max y x
propMaxRefl Z Z = refl
propMaxRefl Z (S y) = refl
propMaxRefl (S x) Z = refl
propMaxRefl (S x) (S y) =
  begin
    max (S x) (S y)
  =⟨ propMaxSuc x y ⟩
    S (max x y)
  =⟨ cong S (propMaxRefl x y) ⟩
    S (max y x)
  =⟨ sym $ propMaxSuc y x ⟩
    max (S y) (S x)
  end

propIsTrueCombine2 : {a b : Bool} -> IsTrue a -> IsTrue b -> IsTrue (a && b)
propIsTrueCombine2 {true} {true} ta tb = IsTrue.itsTrue

propIsTrueCombine4 : {a b c d : Bool} -> IsTrue a -> IsTrue b -> IsTrue c -> IsTrue d -> IsTrue ((a && b) && (c && d))
propIsTrueCombine4 {true} {true} {true} {true} ta tb tc td = IsTrue.itsTrue

propIsTrueCombine4Alt : {a b c d : Bool} -> IsTrue a -> IsTrue b -> IsTrue c -> IsTrue d -> IsTrue (a && b && c && d)
propIsTrueCombine4Alt {true} {true} {true} {true} ta tb tc td = IsTrue.itsTrue

andRefl : (a b : Bool) -> (a && b) ≡ (b && a)
andRefl false false = refl
andRefl false true = refl
andRefl true false = refl
andRefl true true = refl

andFst : {a b : Bool} -> IsTrue (a && b) -> IsTrue a
andFst {true} {true} ab = IsTrue.itsTrue

andSnd : {a b : Bool} -> IsTrue (a && b) -> IsTrue b
andSnd {true} {true} ab = IsTrue.itsTrue

and1 : {a b c d : Bool} -> IsTrue (a && b && c && d) -> IsTrue a
and1 {true} {true} {true} {true} abcd = IsTrue.itsTrue

and2 : {a b c d : Bool} -> IsTrue (a && b && c && d) -> IsTrue b
and2 {true} {true} {true} {true} abcd = IsTrue.itsTrue

and3 : {a b c d : Bool} -> IsTrue (a && b && c && d) -> IsTrue c
and3 {true} {true} {true} {true} abcd = IsTrue.itsTrue

and4 : {a b c d : Bool} -> IsTrue (a && b && c && d) -> IsTrue d
and4 {true} {true} {true} {true} abcd = IsTrue.itsTrue

andCombine : {a b : Bool} -> IsTrue a -> IsTrue b -> IsTrue (a && b)
andCombine {true} {true} ta tb = IsTrue.itsTrue

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
log2up 0 = 0
log2up 1 = 0
log2up x = S (log2up (div (x + 1) 2))
{-# COMPILE AGDA2HS log2up #-}


zeroLteAny : (a : Nat) -> IsTrue (0 <= a)
zeroLteAny Z = IsTrue.itsTrue
zeroLteAny (S a) = IsTrue.itsTrue

lteTransitive : (a b c : Nat) -> IsTrue (a <= b) -> IsTrue (b <= c) -> IsTrue (a <= c)
lteTransitive Z Z c ab bc = bc
lteTransitive Z (S b) (S c) ab bc = IsTrue.itsTrue
lteTransitive (S a) (S b) (S c) ab bc = lteTransitive a b c ab bc

incrLte : (a b : Nat) -> IsTrue (a <= b) -> IsTrue (a <= S b)
incrLte Z Z altb = IsTrue.itsTrue
incrLte Z (S b) altb = IsTrue.itsTrue
incrLte (S a) (S b) altb = incrLte a b altb

natPlusMinNat : (x : Nat) -> {{p : IsFalse (x < 1)}} -> x ≡ (S (x - 1))
natPlusMinNat (S x) = refl

transformLteRight : {a b c : Nat} -> b ≡ c -> IsTrue (a <= b) -> IsTrue (a <= c)
transformLteRight {a} {b} {.b} refl ab = ab

lteSelf : (v : Nat) -> IsTrue (v <= v)
lteSelf Z = IsTrue.itsTrue
lteSelf (S v) = lteSelf v

isFalseNot : {b : Bool} -> IsFalse (not b) -> IsTrue b
isFalseNot {true} if = IsTrue.itsTrue