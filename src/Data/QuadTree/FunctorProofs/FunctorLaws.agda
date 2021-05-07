-- {-# OPTIONS --show-implicit --show-irrelevant #-}
module Data.QuadTree.FunctorProofs.FunctorLaws where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive


-- First, define the Functor laws

IdentityLaw : (f : Set -> Set) -> {{ff : Functor f}} -> Set₁
IdentityLaw f {{ff}} = {t : Set} -> (v : f t) -> fmap id v ≡ id v

CompositionLaw : (f : Set -> Set) -> {{ff : Functor f}} -> Set₁
CompositionLaw f {{ff}} = {a b c : Set} -> (v : f a) -> (fun1 : a -> b) -> (fun2 : b -> c) -> fmap (fun2 ∘ fun1) v ≡ fmap fun2 (fmap fun1 v)

-- Define ValidFunctor as a functor for which the laws hold

data ValidFunctor : Set₁ where
  CValidFunctor : (f : Set -> Set) {{ff : Functor f}} -> IdentityLaw f -> CompositionLaw f -> ValidFunctor
