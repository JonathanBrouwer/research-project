module Data.QuadTree.LensProofs.Test where

open import Haskell.Prelude renaming (zero to Z; suc to S)

-- Define Lens
CLens : Set -> Set -> Set₁
CLens s a = {f : Set -> Set} {{ff : Functor f}} -> (a -> f a) -> s -> f s

-- Define const & identity functors
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

-- Define lens functions
view : {a b : Set} -> CLens a b -> a -> b
view lens v = getConst $ lens CConst v
set : {a b : Set} -> CLens a b -> b -> a -> a
set lens to v = runIdentity $ lens (λ _ -> CIdentity to) v
over : {a b : Set} -> CLens a b -> (b -> b) -> a -> a
over lens f v = runIdentity $ lens (CIdentity ∘ f) v

-- Define lens laws
ViewSet : {a b : Set} -> (l : CLens a b) -> Set
ViewSet {a} {b} l = (v : b) (s : a) -> view l (set l v s) ≡ v
SetView : {a b : Set} -> (l : CLens a b) -> Set
SetView {a} {b} l = (s : a) -> set l (view l s) s ≡ s
SetSet : {a b : Set} -> (l : CLens a b) -> Set
SetSet {a} {b} l = (v1 v2 : b) (s : a) -> set l v2 (set l v1 s) ≡ set l v2 s

-- Define a data class holding a lens and the lens laws
data ValidLens (a b : Set) : Set₁ where
  CValidLens : (l : CLens a b) -> ViewSet l -> SetView l -> SetSet l -> ValidLens a b

toLens : ValidLens a b -> CLens a b
toLens (CValidLens l _ _ _) = l

-- Now for the problem

postulate
    lensA : Bool -> CLens Nat Nat
    vsA : (b : Bool) -> ViewSet (lensA b)
    svA : (b : Bool) -> SetView (lensA b)
    ssA : (b : Bool) -> SetSet (lensA b)

ValidLensA : Bool -> ValidLens Nat Nat
ValidLensA b = CValidLens (lensA b) (vsA b) (svA b) (ssA b)

proof : (b : Bool) -> (s : Nat) -> toLens (ValidLensA b) CConst s ≡ (lensA b) CConst s
proof b s = refl


