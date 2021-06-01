-- {-# OPTIONS --show-implicit --show-irrelevant #-}
module Data.QuadTree.FunctorProofs.Valid-QuadTreeFunctor where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive
open import Data.QuadTree.FunctorProofs.FunctorLaws
open import Data.QuadTree.FunctorProofs.Valid-QuadrantFunctor
open import Data.QuadTree.Implementation.Definition
open import Data.QuadTree.Implementation.ValidTypes
open import Data.QuadTree.Implementation.Functors
open import Data.QuadTree.Implementation.QuadrantLenses

ValidFunctor-QuadTree-IdentityLaw : (dep : Nat) -> IdentityLaw (λ y -> VQuadTree y {dep}) {{quadtreeFunctor dep}}
ValidFunctor-QuadTree-IdentityLaw dep (CVQuadTree (Wrapper (w , h) qd) {p}) =
    begin
        toQt dep w h _ (fmapₑ (quadrantFunctor dep) id (CVQuadrant qd))
    =⟨ cong (toQt dep w h _) (ValidFunctor-Quadrant-IdentityLaw dep (CVQuadrant qd)) ⟩
        toQt dep w h _ (CVQuadrant qd)
    end

toQt-fmap : {a b : Set} {{eqA : Eq a}} {{eqB : Eq b}} (dep w h : Nat) (g : a -> b) (v : VQuadrant a {dep}) .(q : IsTrue (dep == log2up (if w < h then h else w)))
    -> toQt dep w h q (fmapₑ (quadrantFunctor dep) g v) 
    ≡ fmapₑ (quadtreeFunctor dep) g (toQt dep w h q v)
toQt-fmap dep w h g (CVQuadrant (Leaf x)) q = refl
toQt-fmap dep w h g (CVQuadrant (Node qd qd₁ qd₂ qd₃)) q = refl

ValidFunctor-QuadTree-CompositionLaw : (dep : Nat) -> CompositionLaw (λ y -> VQuadTree y {dep}) {{quadtreeFunctor dep}}
ValidFunctor-QuadTree-CompositionLaw dep (CVQuadTree (Wrapper (w , h) qd) {p} {q}) f g =
    begin
        toQt dep w h _ (fmapₑ (quadrantFunctor dep) (g ∘ f) (CVQuadrant qd))
    =⟨ cong (toQt dep w h _) (ValidFunctor-Quadrant-CompositionLaw dep (CVQuadrant qd) f g) ⟩
        toQt dep w h _ (fmapₑ (quadrantFunctor dep) g (fmapₑ (quadrantFunctor dep) f (CVQuadrant qd)))
    =⟨ toQt-fmap dep w h g (fmapₑ (quadrantFunctor dep) f (CVQuadrant qd)) q ⟩
        fmapₑ (quadtreeFunctor dep) g (toQt dep w h _ (fmapₑ (quadrantFunctor dep) f (CVQuadrant qd)))
    end where
        
