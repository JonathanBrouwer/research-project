-- {-# OPTIONS --show-implicit --show-irrelevant #-}
module Data.QuadTree.FunctorProofs.Valid-QuadrantFunctor where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive
open import Data.QuadTree.FunctorProofs.FunctorLaws
open import Data.QuadTree.Implementation.Definition
open import Data.QuadTree.Implementation.ValidTypes
open import Data.QuadTree.Implementation.Functors
open import Data.QuadTree.Implementation.QuadrantLenses

ValidFunctor-Quadrant-IdentityLaw : (dep : Nat) -> IdentityLaw (λ y -> VQuadrant y {dep}) {{quadrantFunctor dep}}
ValidFunctor-Quadrant-IdentityLaw dep (CVQuadrant (Leaf v)) = refl
ValidFunctor-Quadrant-IdentityLaw dep@(S deps) (CVQuadrant qd@(Node (Leaf a) (Leaf b) (Leaf c) (Leaf d)) {p}) = 
    ifcFalse (a == b && b == c && c == d) (notTrueToFalse $ andSndI {a = (depth qd <= dep)} p)
ValidFunctor-Quadrant-IdentityLaw dep@(S deps) (CVQuadrant (Node a@(Leaf _) b@(Leaf _) c@(Leaf _) d@(Node _ _ _ _)) {p}) = 
    cong (combine (CVQuadrant a) (CVQuadrant b) (CVQuadrant c)) 
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant d))
ValidFunctor-Quadrant-IdentityLaw dep@(S deps) (CVQuadrant (Node a@(Leaf _) b@(Leaf _) c@(Node _ _ _ _) d) {p}) =
    cong2 (combine (CVQuadrant a) (CVQuadrant b)) 
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant c))
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant d))
ValidFunctor-Quadrant-IdentityLaw dep@(S deps) (CVQuadrant (Node a@(Leaf _) b@(Node _ _ _ _) c d) {p}) =
    cong3 (combine (CVQuadrant a)) 
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant b))
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant c))
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant d))
ValidFunctor-Quadrant-IdentityLaw dep@(S deps) (CVQuadrant (Node a@(Node _ _ _ _) b c d) {p}) =
    cong4 combine
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant a))
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant b))
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant c))
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant d))
  

postulate
    eq-subst : {a b : Set} {{eqA : Eq a}} {{eqB : Eq b}} -> (f : a -> b) -> (x y : a)
        -> (x == y) ≡ (f x == f y)

ValidFunctor-Quadrant-CompositionLaw : (dep : Nat) -> CompositionLaw (λ y -> VQuadrant y {dep}) {{quadrantFunctor dep}}
ValidFunctor-Quadrant-CompositionLaw dep (CVQuadrant (Leaf x)) f g = refl
ValidFunctor-Quadrant-CompositionLaw dep@(S deps) {t1} {t2} {t3} cvq@(CVQuadrant qd@(Node a@(Leaf va) b@(Leaf vb) c@(Leaf vc) d@(Leaf vd)) {p}) f g = 
    begin
        fmapₑ (quadrantFunctor dep) g cvq-from
    =⟨ sym (cong (λ q -> fmapₑ (quadrantFunctor dep) g q) p2)  ⟩ 
        fmapₑ (quadrantFunctor dep) g cvq-to
    end where
        map-f-ABC = cong3 (λ e1 e2 e3 -> e1 && e2 && e3) (eq-subst f va vb) (eq-subst f vb vc) (eq-subst f vc vd)
        cvq-from = (CVQuadrant (Node (Leaf (f va)) (Leaf (f vb)) (Leaf (f vc)) (Leaf (f vd))) 
            {andCombine (zeroLteAny deps) (useEq (cong not map-f-ABC) (andSndI {a = (depth qd <= dep)} p))})
        cvq-to = ifc (f va == f vb) && (f vb == f vc) && (f vc == f vd) then (CVQuadrant (Leaf (f va))) else (CVQuadrant (Node (Leaf (f va)) (Leaf (f vb)) (Leaf (f vc)) (Leaf (f vd))))
        p2 : cvq-to ≡ cvq-from
        p2 = (ifcFalse ((f va == f vb) && (f vb == f vc) && (f vc == f vd)) 
            (useEqFalse 
                (cong3 (λ e1 e2 e3 -> e1 && e2 && e3) (eq-subst f va vb) (eq-subst f vb vc) (eq-subst f vc vd)) 
                (notTrueToFalse $ andSndI {a = (depth qd <= dep)} p)))
ValidFunctor-Quadrant-CompositionLaw dep@(S deps) cvq@(CVQuadrant (Node a@(Leaf _) b@(Leaf _) c@(Leaf _) d@(Node _ _ _ _)) {p}) f g = {!   !}
ValidFunctor-Quadrant-CompositionLaw dep@(S deps) cvq@(CVQuadrant (Node a@(Leaf _) b@(Leaf _) c@(Node _ _ _ _) d) {p}) f g = {!   !}
ValidFunctor-Quadrant-CompositionLaw dep@(S deps) cvq@(CVQuadrant (Node a@(Leaf _) b@(Node _ _ _ _) c d) {p}) f g = {!   !}
ValidFunctor-Quadrant-CompositionLaw dep@(S deps) cvq@(CVQuadrant (Node a@(Node _ _ _ _) b c d) {p}) f g = {!   !}
    -- begin
    --     combine
    --         (fmapₑ (quadrantFunctor deps) (g ∘ f) (CVQuadrant a))
    --         (fmapₑ (quadrantFunctor deps) (g ∘ f) (CVQuadrant b))
    --         (fmapₑ (quadrantFunctor deps) (g ∘ f) (CVQuadrant c))
    --         (fmapₑ (quadrantFunctor deps) (g ∘ f) (CVQuadrant d))
    -- =⟨ {!  refl !} ⟩
    --     fmapₑ (quadrantFunctor (S deps)) g
    --         (combine
    --             (fmapₑ (quadrantFunctor deps) f (CVQuadrant a))
    --             (fmapₑ (quadrantFunctor deps) f (CVQuadrant b))
    --             (fmapₑ (quadrantFunctor deps) f (CVQuadrant c))
    --             (fmapₑ (quadrantFunctor deps) f (CVQuadrant d)) )
    -- end
