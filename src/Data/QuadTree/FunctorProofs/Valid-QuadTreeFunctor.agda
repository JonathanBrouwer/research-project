-- {-# OPTIONS --show-implicit --show-irrelevant #-}
module Data.QuadTree.FunctorProofs.Valid-QuadTreeFunctor where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive
open import Data.QuadTree.FunctorProofs.FunctorLaws
open import Data.QuadTree.FunctorProofs.Valid-QuadrantFunctor

ValidFunctor-QuadTree-IdentityLaw : 
    IdentityLaw QuadTree
ValidFunctor-QuadTree-IdentityLaw (Wrapper (x , y) qd) = cong (λ q -> Wrapper (x , y) q) (ValidFunctor-Quadrant-IdentityLaw qd)

ValidFunctor-QuadTree-CompositionLaw : 
    CompositionLaw QuadTree
ValidFunctor-QuadTree-CompositionLaw (Wrapper (x , y) qd) f g = cong (λ q -> Wrapper (x , y) q) (ValidFunctor-Quadrant-CompositionLaw qd f g)


ValidFunctor-QuadTree : ValidFunctor
ValidFunctor-QuadTree = CValidFunctor QuadTree (ValidFunctor-QuadTree-IdentityLaw) (ValidFunctor-QuadTree-CompositionLaw)