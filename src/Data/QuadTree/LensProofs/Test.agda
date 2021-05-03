{-# OPTIONS --show-implicit --show-irrelevant #-}
module Data.QuadTree.LensProofs.Test where

open import Agda.Primitive
open import Haskell.Prelude renaming (zero to Z; suc to S)

---- Equational reasoning stuff
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl
cong : {u v : Level} {A : Set u} {B : Set v} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
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

---- Functors

data Const (a : Set) (b : Set) : Set where
  CConst : a -> Const a b
getConst : {a : Set} {b : Set} -> Const a b -> a
getConst (CConst a) = a
instance
  constFunctor : {a : Set} -> Functor (Const a)
  constFunctor .fmap f (CConst v) = CConst v
data Identity (a : Set) : Set where
  CIdentity : a -> Identity a
runIdentity : {a : Set} -> Identity a -> a
runIdentity (CIdentity a) = a
instance
  identityFunctor : Functor Identity
  identityFunctor .fmap f (CIdentity v) = CIdentity (f v)

---- Lens
-- van Laarhoven style implementation

CLens : Set -> Set -> Set₁
CLens s a = {f : Set -> Set} -> {{ff : Functor f}} -> (a -> f a) -> s -> f s
view : {a b : Set} -> CLens a b -> a -> b
view lens v = getConst $ lens CConst v
set : {a b : Set} -> CLens a b -> b -> a -> a
set lens to v = runIdentity $ lens (λ _ -> CIdentity to) v
over : {a b : Set} -> CLens a b -> (b -> b) -> a -> a
over lens f v = runIdentity $ lens (CIdentity ∘ f) v



--------------------------------------------------------------------------
--- Here the real challenge starts

-- Two identity lenses
testA : CLens Nat Nat
testA f v = f v
testB : CLens Nat Nat
testB f v = f v

-- Choses one based on a Nat
testAB : Nat -> CLens Nat Nat
testAB n f v = (if n < 324 then testA f v else testB f v)

-- Hints:
-- * view testA (set testA v s) ≡ v can be proven using refl
-- * view testB (set testB v s) ≡ v can be proven using refl
-- * The error refers to implicit arguments of cong


-- cool : (n v s : Nat) -> testAB n ≡ {! testAB n  !}
-- cool = {!   !}

-- proof : (n v s : Nat) -> view (testAB n) (set (testAB n) v s) ≡ v
-- proof n v s =
--     begin
--         view (testAB n) (set (testAB n) v s)
--     =⟨ {!   !} ⟩
--         v
--     end
