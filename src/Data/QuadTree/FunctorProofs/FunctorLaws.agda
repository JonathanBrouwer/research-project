-- {-# OPTIONS --show-implicit --show-irrelevant #-}
module Data.QuadTree.FunctorProofs.FunctorLaws where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive
open import Data.QuadTree.Implementation.Functors


-- First, define the Functor laws

IdentityLaw : (f : (t : Set) -> {{ eqT : Eq t }} -> Set) -> {{ff : FunctorEq f}} -> Set₁
IdentityLaw f {{ff}} = {t : Set} -> {{ eqT : Eq t }} 
  -> (v : f t) -> fmapₑ ff id v ≡ id v

CompositionLaw : (f : (t : Set) -> {{ eqT : Eq t }} -> Set) -> {{ff : FunctorEq f}} -> Set₁
CompositionLaw f {{ff}} = {a b c : Set} -> {{ eqA : Eq a }} {{ eqB : Eq b }} {{ eqC : Eq c }} 
  -> (v : f a) -> (fun1 : a -> b) -> (fun2 : b -> c) -> fmapₑ ff (fun2 ∘ fun1) v ≡ fmapₑ ff fun2 (fmapₑ ff fun1 v)
