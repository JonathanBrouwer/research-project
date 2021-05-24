-- {-# OPTIONS --show-implicit --show-irrelevant #-}
module Data.QuadTree.FunctorProofs.Valid-QuadrantFunctor where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive
open import Data.QuadTree.FunctorProofs.FunctorLaws
open import Data.QuadTree.Implementation.Definition
open import Data.QuadTree.Implementation.Functors

ValidFunctor-Quadrant-IdentityLaw : 
    IdentityLaw Quadrant
ValidFunctor-Quadrant-IdentityLaw (Leaf x) = refl
ValidFunctor-Quadrant-IdentityLaw (Node a b c d) = 
    begin
        Node (fmap id a) (fmap id b) (fmap id c) (fmap id d)
    =⟨ cong (λ g -> Node g (fmap id b) (fmap id c) (fmap id d)) ((ValidFunctor-Quadrant-IdentityLaw a)) ⟩
        Node a (fmap id b) (fmap id c) (fmap id d)
    =⟨ cong (λ g -> Node a g (fmap id c) (fmap id d)) ((ValidFunctor-Quadrant-IdentityLaw b)) ⟩
        Node a b (fmap id c) (fmap id d)
    =⟨ cong (λ g -> Node a b g (fmap id d)) ((ValidFunctor-Quadrant-IdentityLaw c)) ⟩
        Node a b c (fmap id d)
    =⟨ cong (λ g -> Node a b c g) ((ValidFunctor-Quadrant-IdentityLaw d)) ⟩
        id (Node a b c d)
    end

ValidFunctor-Quadrant-CompositionLaw : 
    CompositionLaw Quadrant
ValidFunctor-Quadrant-CompositionLaw (Leaf x) f g = refl
ValidFunctor-Quadrant-CompositionLaw (Node a b c d) f g =
    begin
        Node (fmap (g ∘ f) a) (fmap (g ∘ f) b) (fmap (g ∘ f) c) (fmap (g ∘ f) d)
    =⟨ cong (λ q -> Node q (fmap (g ∘ f) b) (fmap (g ∘ f) c) (fmap (g ∘ f) d)) (ValidFunctor-Quadrant-CompositionLaw a f g) ⟩
        (Node (fmap g (fmap f a)) (fmap (g ∘ f) b) (fmap (g ∘ f) c) (fmap (g ∘ f) d))
    =⟨ cong (λ q -> Node (fmap g (fmap f a)) q (fmap (g ∘ f) c) (fmap (g ∘ f) d)) (ValidFunctor-Quadrant-CompositionLaw b f g) ⟩
        (Node (fmap g (fmap f a)) (fmap g (fmap f b)) (fmap (g ∘ f) c) (fmap (g ∘ f) d))
    =⟨ cong (λ q -> Node (fmap g (fmap f a)) (fmap g (fmap f b)) q (fmap (g ∘ f) d)) (ValidFunctor-Quadrant-CompositionLaw c f g) ⟩
        (Node (fmap g (fmap f a)) (fmap g (fmap f b)) (fmap g (fmap f c)) (fmap (g ∘ f) d))
    =⟨ cong (λ q -> Node (fmap g (fmap f a)) (fmap g (fmap f b)) (fmap g (fmap f c)) q) (ValidFunctor-Quadrant-CompositionLaw d f g) ⟩
        (Node (fmap g (fmap f a)) (fmap g (fmap f b)) (fmap g (fmap f c)) (fmap g (fmap f d)))
    =⟨⟩
        fmap g (fmap f (Node a b c d))
    end


ValidFunctor-Quadrant : ValidFunctor
ValidFunctor-Quadrant = CValidFunctor Quadrant (ValidFunctor-Quadrant-IdentityLaw) (ValidFunctor-Quadrant-CompositionLaw)