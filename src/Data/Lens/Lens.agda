module Data.Lens.Lens where

open import Haskell.Prelude

{-# FOREIGN AGDA2HS
{-# LANGUAGE Rank2Types #-}
#-}

---- Functors

-- The const functor, for which fmap does not change its value

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

-- The identity functor, which just wraps the object

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

---- Lens
-- van Laarhoven style implementation

CLens : Set -> Set -> Set₁
CLens s a = {f : Set -> Set} {{ff : Functor f}} -> (a -> f a) -> s -> f s
{-# FOREIGN AGDA2HS type CLens s a = forall f. Functor f => (a -> f a) -> s -> f s #-}

view : {a b : Set} -> CLens a b -> a -> b
view lens v = getConst $ lens CConst v
{-# COMPILE AGDA2HS view #-}

set : {a b : Set} -> CLens a b -> b -> a -> a
set lens to v = runIdentity $ lens (λ _ -> CIdentity to) v
{-# COMPILE AGDA2HS set #-}

over : {a b : Set} -> CLens a b -> (b -> b) -> a -> a
over lens f v = runIdentity $ lens (CIdentity ∘ f) v
{-# COMPILE AGDA2HS over #-}