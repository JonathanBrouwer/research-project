module Data.Logic where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Relation.Nullary.Decidable
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Agda.Primitive
{-# FOREIGN AGDA2HS
import Data.Nat
#-}


---- Equational reasoning
useEq : {x y : Bool} -> x ≡ y -> IsTrue x -> IsTrue y
useEq {true} {true} eq is = IsTrue.itsTrue

-- symmetry of equality
sym : {u : Level} {A : Set u} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- transitivity of equality
trans : {u : Level} {A : Set u} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

-- congruence of equality
cong : {u v : Level} {A : Set u} {B : Set v} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

begin_ : {u : Level} {A : Set u} → {x y : A} → x ≡ y → x ≡ y
begin p = p

_end : {u : Level} {A : Set u} → (x : A) → x ≡ x
x end = refl

_=⟨_⟩_ : {u : Level} {A : Set u} → (x : A) → {y z : A}
       → x ≡ y → y ≡ z → x ≡ z
x =⟨ p ⟩ q = trans p q

_=⟨⟩_ : {u : Level} {A : Set u} → (x : A) → {y : A} → x ≡ y → x ≡ y
x =⟨⟩ q = x =⟨ refl ⟩ q

infix   1  begin_
infix   3  _end
infixr  2  _=⟨_⟩_
infixr  2  _=⟨⟩_

---- General purpose proofs

propZeroImpliesLtOne : (x : Nat) -> IsFalse (x == 0) -> IsFalse (x < 1)
propZeroImpliesLtOne Z notZ = notZ
propZeroImpliesLtOne (S x) notZ = IsFalse.itsFalse

propFnIf : {a b : Set} -> {c : Bool} {x y : a} (f : a -> b) -> (if c then f x else f y) ≡ f (if c then x else y)
propFnIf {c = false} f = refl
propFnIf {c = true} f = refl

propMaxSuc : (x y : Nat) -> max (S x) (S y) ≡ S (max x y)
propMaxSuc Z Z = refl
propMaxSuc Z (S y) = refl
propMaxSuc (S x) Z = refl
propMaxSuc (S x) (S y) =
  begin
    max (S $ S x) (S $ S y)
  =⟨⟩
    (if x < y then (S $ S y) else (S $ S x))
  =⟨ propFnIf S ⟩
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

ifTrue : {u : Level} {t : Set u} {a b : t} (c : Bool) -> IsTrue c -> (if c then a else b) ≡ a
ifTrue true tc = refl

ifFalse : {t : Set} {a b : t} (c : Bool) -> IsFalse c -> (if c then a else b) ≡ b
ifFalse false fc = refl

infix -2 ifc_then_else_
ifc_then_else_ : {u : Level} {a : Set u} → (c : Bool) → ({{IsTrue c}} → a) → ({{IsFalse c}} → a) → a
ifc false then x else y = y {{IsFalse.itsFalse}}
ifc true then x else y = x {{IsTrue.itsTrue}}
{-# COMPILE AGDA2HS ifc_then_else_ #-}

ifcTrue : {u : Level} {t : Set u} -> (c : Bool) {a : {{.(IsTrue c)}} -> t} {b : {{.(IsFalse c)}} -> t} -> .(ct : IsTrue c) -> (ifc c then (λ {{p}} -> a) else (λ {{p}} -> b)) ≡ (a {{ct}})
ifcTrue true {a} {b} ct = refl

ifcFalse : {u : Level} {t : Set u} -> (c : Bool) {a : {{.(IsTrue c)}} -> t} {b : {{.(IsFalse c)}} -> t} -> .(ct : IsFalse c) -> (ifc c then (λ {{p}} -> a) else (λ {{p}} -> b)) ≡ (b {{ct}})
ifcFalse false {a} {b} ct = refl

propFnIfc : {a b : Set} -> (c : Bool) {x : {{IsTrue c}} -> a} {y : {{IsFalse c}} -> a} (f : a -> b) 
  -> (ifc c then f x else f y) ≡ f (ifc c then x else y)
propFnIfc false f = refl
propFnIfc true f = refl

propFnDistributeIfc2 : {a b : Set} -> (c1 c2 : Bool) {w x y z : a} (f : a -> b) 
  -> f (ifc c1 then (ifc c2 then w else x) else (ifc c2 then y else z))
  ≡ (ifc c1 then (ifc c2 then f w else f x) else (ifc c2 then f y else f z))
propFnDistributeIfc2 false false f = refl
propFnDistributeIfc2 false true f = refl
propFnDistributeIfc2 true false f = refl
propFnDistributeIfc2 true true f = refl

propIfcBranchesSame : {t : Set} -> {c : Bool} (v : t)
  -> (ifc c then v else v) ≡ v
propIfcBranchesSame {c = false} v = refl
propIfcBranchesSame {c = true} v = refl

propIfBranchesSame : {t : Set} -> {c : Bool} (v : t)
  -> (if c then v else v) ≡ v
propIfBranchesSame {c = false} v = refl
propIfBranchesSame {c = true} v = refl

ifToIfc : {t : Set} {c : Bool} {a b : t} -> (if c then a else b) ≡ (ifc c then a else b)
ifToIfc {c = false} = refl
ifToIfc {c = true} = refl

ifTrueMap : {t : Set} -> {c : Bool} {a a2 b : t} -> (IsTrue c -> a ≡ a2) -> (if c then a else b) ≡ (if c then a2 else b)
ifTrueMap {c = false} aa2 = refl
ifTrueMap {c = true} {a} {a2} aa2 = 
  begin
    a
  =⟨ aa2 IsTrue.itsTrue ⟩
    a2
  end

ifcTrueMap : {t : Set} -> {c : Bool} {a a2 b : t} -> (IsTrue c -> a ≡ a2) -> (ifc c then a else b) ≡ (ifc c then a2 else b)
ifcTrueMap {c = false} aa2 = refl
ifcTrueMap {c = true} {a} {a2} aa2 = 
  begin
    a
  =⟨ aa2 IsTrue.itsTrue ⟩
    a2
  end
  
ifTrueNested : {t : Set} -> {c1 c2 : Bool} {a b c : t} -> (c1 ≡ c2) -> (if c1 then (if c2 then a else b) else c) ≡ (if c1 then a else c)
ifTrueNested {t} {false} {false} {a} {b} {c} c1eqc2 = refl
ifTrueNested {t} {true} {true} {a} {b} {c} c1eqc2 = refl

ifFalseNested : {t : Set} -> {c1 c2 : Bool} {a b c : t} -> (c1 ≡ c2) -> (if c1 then a else (if c2 then b else c)) ≡ (if c1 then a else c)
ifFalseNested {t} {false} {false} {a} {b} {c} c1eqc2 = refl
ifFalseNested {t} {true} {true} {a} {b} {c} c1eqc2 = refl

---- Useful functions

div : Nat -> (divisor : Nat) -> {≢0 : False (divisor ≟ 0)} -> Nat
div a b {p} = _/_ a b {p}
-- Does not need compile, since it is already defined in haskell

mod : Nat -> (divisor : Nat) -> {≢0 : False (divisor ≟ 0)} -> Nat
mod a b {p} = _%_ a b {p}
-- Does not need compile, since it is already defined in haskell

pow : Nat -> Nat -> Nat
pow b Z = 1
pow b (S e) = b * pow b e
{-# COMPILE AGDA2HS pow #-}

mul_not_zero : {a b : Nat} -> IsFalse (a == 0) -> IsFalse (b == 0) -> IsFalse (a * b == 0)
mul_not_zero {S a} {S b} az bz = IsFalse.itsFalse

pow_not_zero : (n : Nat) -> IsFalse (pow 2 n == 0)
pow_not_zero Z = IsFalse.itsFalse
pow_not_zero (S sn) = mul_not_zero {2} {pow 2 sn} IsFalse.itsFalse (pow_not_zero sn)

false_convert : (n : Nat) -> IsFalse (n == 0) -> False (n ≟ 0)
false_convert (S n) if = tt

pow_not_zero_cv : (n : Nat) -> False (pow 2 n ≟ 0) 
pow_not_zero_cv n = false_convert (pow 2 n) $ pow_not_zero n

zeroLteAny : (a : Nat) -> IsTrue (0 <= a)
zeroLteAny Z = IsTrue.itsTrue
zeroLteAny (S a) = IsTrue.itsTrue

anyGteZero : (a : Nat) -> IsTrue (a >= 0)
anyGteZero Z = IsTrue.itsTrue
anyGteZero (S a) = IsTrue.itsTrue

{-# TERMINATING #-}
log2up : Nat -> Nat
-- UNSAFE: This terminates since x/2 always decreases if x > 1
log2up 0 = 0
log2up 1 = 0
log2up (S (S x)) = S (log2up (div (S (S (S x))) 2))
{-# COMPILE AGDA2HS log2up #-}

divHelperReduce : (x a b c : Nat) -> div-helper (S x) a b c ≡ S (div-helper x a b c)
divHelperReduce x a Z c = refl
divHelperReduce x a (S b) Z =
  begin
    div-helper (S (S x)) a b a
  =⟨ divHelperReduce (S x) a b a ⟩
    S (div-helper (S x) a b a)
  end
divHelperReduce x a (S b) (S c) = divHelperReduce x a b c

div2Reduce : {x : Nat} -> div (2 + x) 2 ≡ S (div x 2)
div2Reduce {Z} = refl
div2Reduce {x@(S sx)} =
  begin
    div (2 + x) 2
  =⟨⟩
    div-helper 1 1 sx 0
  =⟨ divHelperReduce 0 1 sx 0 ⟩
    S (div-helper 0 1 sx 0)
  =⟨⟩
    S (div x 2)
  end

isTrueEquiv : {b : Bool} -> IsTrue b -> true ≡ b
isTrueEquiv {true} t = refl

plusGteOne : (a b : Nat) -> IsTrue (a >= 1) -> IsTrue (a + b >= 1)
plusGteOne (S a) b p = anyGteZero (a + b)

multGteOne : (a b : Nat) -> IsTrue (a >= 1) -> IsTrue (b >= 1) -> IsTrue (a * b >= 1)
multGteOne (S a) (S b) pa pb = plusGteOne (S b) (a * (S b)) pb

powGteOne : (n : Nat) -> IsTrue (pow 2 n >= 1)
powGteOne Z = IsTrue.itsTrue
powGteOne (S n) = multGteOne 2 (pow 2 n) IsTrue.itsTrue (powGteOne n)

log2upPow : (a b : Nat) -> (a >= log2up b) ≡ (pow 2 a >= b)
log2upPow Z Z = refl
log2upPow Z (S Z) = refl
log2upPow Z (S (S b)) = refl
log2upPow (S a) Z = isTrueEquiv $ anyGteZero (pow 2 (S a))
log2upPow (S a) (S Z) =
  begin
    (S a) >= 0
  =⟨ isTrueEquiv $ anyGteZero (S a) ⟩
    true
  =⟨ isTrueEquiv $ powGteOne (S a) ⟩
    pow 2 (S a) >= 1
  end
log2upPow (S a) (S (S b)) = {!   !}
-- log2upPow {S a} {S (S b)} p = useEq (
--   begin 
--     S a >= log2up (S (S b)) 
--   =⟨⟩
--     a == log2up (div (3 + b) 2)
--   =⟨ cong (λ q -> a == log2up q) (div2Reduce {1 + b}) ⟩
--     a == log2up (S (div (1 + b) 2))
--   =⟨ {! log2upPow {a} {S b} !} ⟩ 
--     {!   !}
--   =⟨ {!   !} ⟩
--     pow 2 (S a) >= (S (S b)) 
--   end) p


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

falseToNotTrue : {b : Bool} -> IsFalse (b) -> IsTrue (not b)
falseToNotTrue {false} if = IsTrue.itsTrue

notFalseToTrue : {b : Bool} -> IsFalse (not b) -> IsTrue b
notFalseToTrue {true} if = IsTrue.itsTrue

trueToNotFalse : {b : Bool} -> IsTrue (b) -> IsFalse (not b)
trueToNotFalse {true} if = IsFalse.itsFalse

notTrueToFalse : {b : Bool} -> IsTrue (not b) -> IsFalse (b)
notTrueToFalse {false} if = IsFalse.itsFalse

-- Law of reflexivity for equality
postulate
  eqReflexivity : {t : Set} {{eqT : Eq t}} (v : t) -> IsTrue (v == v)
  eqToEquiv : {t : Set} {{eqT : Eq t}} (a b : t) -> IsTrue (a == b) -> a ≡ b

botToAny : {t : Set} -> ⊥ -> t
botToAny ()

impossible : {t : Set} -> t
impossible = botToAny bot where
  postulate bot : ⊥
{-# FOREIGN AGDA2HS impossible = error "Impossible" #-}

max4 : (a b c d : Nat) -> Nat
max4 a b c d = max (max a b) (max c d)
{-# COMPILE AGDA2HS max4 #-}