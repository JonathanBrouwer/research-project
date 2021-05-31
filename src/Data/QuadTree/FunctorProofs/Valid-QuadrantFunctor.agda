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
    cong4 combine
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant a))
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant b))
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant c))
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant d))
ValidFunctor-Quadrant-IdentityLaw dep@(S deps) (CVQuadrant (Node a@(Leaf _) b@(Leaf _) c@(Node _ _ _ _) d) {p}) =
    cong4 combine
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant a))
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant b))
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant c))
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant d))
ValidFunctor-Quadrant-IdentityLaw dep@(S deps) (CVQuadrant (Node a@(Leaf _) b@(Node _ _ _ _) c d) {p}) =
    cong4 combine
        (ValidFunctor-Quadrant-IdentityLaw deps (CVQuadrant a))
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

combine-fmap : {t s : Set} {{eqT : Eq t}} {{eqS : Eq s}} {dep : Nat} -> (a b c d : VQuadrant t {dep})
    -> (f : t -> s)
    -> combine (fmapₑ (quadrantFunctor dep) f a) (fmapₑ (quadrantFunctor dep) f b) (fmapₑ (quadrantFunctor dep) f c) (fmapₑ (quadrantFunctor dep) f d)
        ≡ fmapₑ (quadrantFunctor (S dep)) f (combine a b c d)
combine-fmap {t} {s} {dep = dep} (CVQuadrant a@(Leaf va)) (CVQuadrant b@(Leaf vb)) (CVQuadrant c@(Leaf vc)) (CVQuadrant d@(Leaf vd)) f =
    ifc (va == vb && vb == vc && vc == vd) 
    then (λ {{p}} -> 
        begin
            (ifc (f va == f vb) && (f vb == f vc) && (f vc == f vd) then _ else _)
        =⟨ ifcTrue _ (useEq (cong3 (λ e1 e2 e3 -> e1 && e2 && e3) (eq-subst f va vb) (eq-subst f vb vc) (eq-subst f vc vd)) p) ⟩
            fmapₑ (quadrantFunctor (S dep)) f (CVQuadrant (Leaf va))
        =⟨ cong (fmapₑ (quadrantFunctor (S dep)) f) (sym $ ifcTrue ((va == vb) && (vb == vc) && (vc == vd)) p) ⟩
            fmapₑ (quadrantFunctor (S dep)) f (ifc (va == vb) && (vb == vc) && (vc == vd) then CVQuadrant (Leaf va) else CVQuadrant (Node (Leaf va) (Leaf vb) (Leaf vc) (Leaf vd)))
        end) 
    else (λ {{p}} -> 
        begin
            (ifc (f va == f vb) && (f vb == f vc) && (f vc == f vd) then _ else _)
        =⟨ sym $ cong 
            {y = (CVQuadrant (Node (Leaf va) (Leaf vb) (Leaf vc) (Leaf vd)) {andCombine (zeroLteAny dep) (falseToNotTrue p)})}
            p1 (ifcFalse ((va == vb) && (vb == vc) && (vc == vd)) p) ⟩
            fmapₑ (quadrantFunctor (S dep)) f (ifc (va == vb) && (vb == vc) && (vc == vd) then CVQuadrant (Leaf va) else CVQuadrant (Node (Leaf va) (Leaf vb) (Leaf vc) (Leaf vd)))
        end) where
    p1 : VQuadrant t {S dep} -> VQuadrant s {S dep}
    p1 q = (fmapₑ (quadrantFunctor (S dep)) f) q
combine-fmap (CVQuadrant (Leaf _)) (CVQuadrant (Leaf _)) (CVQuadrant (Leaf _)) (CVQuadrant (Node _ _ _ _)) f = refl
combine-fmap (CVQuadrant (Leaf _)) (CVQuadrant (Leaf _)) (CVQuadrant (Node _ _ _ _)) (CVQuadrant d) f = refl
combine-fmap (CVQuadrant (Leaf _)) (CVQuadrant (Node _ _ _ _)) (CVQuadrant c) (CVQuadrant d) f = refl
combine-fmap (CVQuadrant (Node _ _ _ _)) (CVQuadrant b) (CVQuadrant c) (CVQuadrant d) f = refl

ValidFunctor-Quadrant-CompositionLaw : (dep : Nat) -> CompositionLaw (λ y -> VQuadrant y {dep}) {{quadrantFunctor dep}}
ValidFunctor-Quadrant-CompositionLaw dep (CVQuadrant (Leaf x)) f g = refl
ValidFunctor-Quadrant-CompositionLaw dep@(S deps) {t1} {t2} {t3} cvq@(CVQuadrant qd@(Node a@(Leaf va) b@(Leaf vb) c@(Leaf vc) d@(Leaf vd)) {p}) f g = 
    begin
        combine (mgf sa) (mgf sb) (mgf sc) (mgf sd)
    =⟨ cong4 combine 
        (ValidFunctor-Quadrant-CompositionLaw deps sa f g)
        (ValidFunctor-Quadrant-CompositionLaw deps sb f g) 
        (ValidFunctor-Quadrant-CompositionLaw deps sc f g) 
        (ValidFunctor-Quadrant-CompositionLaw deps sd f g) ⟩
        combine (mg $ mf sa) (mg $ mf sb) (mg $ mf sc) (mg $ mf sd)
    =⟨ combine-fmap (mf sa) (mf sb) (mf sc) (mf sd) g ⟩
        fmapₑ (quadrantFunctor dep) g (combine (mf sa) (mf sb) (mf sc) (mf sd))
    end where
        mf = fmapₑ (quadrantFunctor deps) f
        mg = fmapₑ (quadrantFunctor deps) g
        mgf = fmapₑ (quadrantFunctor deps) (g ∘ f)
        sa = (CVQuadrant a {aSub {dep = deps} a b c d p})
        sb = (CVQuadrant b {bSub {dep = deps} a b c d p})
        sc = (CVQuadrant c {cSub {dep = deps} a b c d p})
        sd = (CVQuadrant d {dSub {dep = deps} a b c d p})
ValidFunctor-Quadrant-CompositionLaw dep@(S deps) cvq@(CVQuadrant (Node a@(Leaf va) b@(Leaf vb) c@(Leaf vc) d@(Node _ _ _ _)) {p}) f g =
    begin
        combine (mgf sa) (mgf sb) (mgf sc) (mgf sd)
    =⟨ cong4 combine 
        (ValidFunctor-Quadrant-CompositionLaw deps sa f g)
        (ValidFunctor-Quadrant-CompositionLaw deps sb f g) 
        (ValidFunctor-Quadrant-CompositionLaw deps sc f g) 
        (ValidFunctor-Quadrant-CompositionLaw deps sd f g) ⟩
        combine (mg $ mf sa) (mg $ mf sb) (mg $ mf sc) (mg $ mf sd)
    =⟨ combine-fmap (mf sa) (mf sb) (mf sc) (mf sd) g ⟩
        fmapₑ (quadrantFunctor dep) g (combine (mf sa) (mf sb) (mf sc) (mf sd))
    end where
        mf = fmapₑ (quadrantFunctor deps) f
        mg = fmapₑ (quadrantFunctor deps) g
        mgf = fmapₑ (quadrantFunctor deps) (g ∘ f)
        sa = (CVQuadrant a {aSub {dep = deps} a b c d p})
        sb = (CVQuadrant b {bSub {dep = deps} a b c d p})
        sc = (CVQuadrant c {cSub {dep = deps} a b c d p})
        sd = (CVQuadrant d {dSub {dep = deps} a b c d p})
ValidFunctor-Quadrant-CompositionLaw dep@(S deps) cvq@(CVQuadrant (Node a@(Leaf _) b@(Leaf _) c@(Node _ _ _ _) d) {p}) f g =
    trans
        (cong4 combine 
            (ValidFunctor-Quadrant-CompositionLaw deps sa f g)
            (ValidFunctor-Quadrant-CompositionLaw deps sb f g) 
            (ValidFunctor-Quadrant-CompositionLaw deps sc f g) 
            (ValidFunctor-Quadrant-CompositionLaw deps sd f g))
        (combine-fmap (mf sa) (mf sb) (mf sc) (mf sd) g)
    where
        mf = fmapₑ (quadrantFunctor deps) f
        sa = (CVQuadrant a {aSub {dep = deps} a b c d p})
        sb = (CVQuadrant b {bSub {dep = deps} a b c d p})
        sc = (CVQuadrant c {cSub {dep = deps} a b c d p})
        sd = (CVQuadrant d {dSub {dep = deps} a b c d p})
ValidFunctor-Quadrant-CompositionLaw dep@(S deps) cvq@(CVQuadrant (Node a@(Leaf _) b@(Node _ _ _ _) c d) {p}) f g =
    trans
        (cong4 combine 
            (ValidFunctor-Quadrant-CompositionLaw deps sa f g)
            (ValidFunctor-Quadrant-CompositionLaw deps sb f g) 
            (ValidFunctor-Quadrant-CompositionLaw deps sc f g) 
            (ValidFunctor-Quadrant-CompositionLaw deps sd f g))
        (combine-fmap (mf sa) (mf sb) (mf sc) (mf sd) g)
    where
        mf = fmapₑ (quadrantFunctor deps) f
        sa = (CVQuadrant a {aSub {dep = deps} a b c d p})
        sb = (CVQuadrant b {bSub {dep = deps} a b c d p})
        sc = (CVQuadrant c {cSub {dep = deps} a b c d p})
        sd = (CVQuadrant d {dSub {dep = deps} a b c d p})
ValidFunctor-Quadrant-CompositionLaw dep@(S deps) cvq@(CVQuadrant (Node a@(Node _ _ _ _) b c d) {p}) f g =
    trans
        (cong4 combine 
            (ValidFunctor-Quadrant-CompositionLaw deps sa f g)
            (ValidFunctor-Quadrant-CompositionLaw deps sb f g) 
            (ValidFunctor-Quadrant-CompositionLaw deps sc f g) 
            (ValidFunctor-Quadrant-CompositionLaw deps sd f g))
        (combine-fmap (mf sa) (mf sb) (mf sc) (mf sd) g)
    where
        mf = fmapₑ (quadrantFunctor deps) f
        sa = (CVQuadrant a {aSub {dep = deps} a b c d p})
        sb = (CVQuadrant b {bSub {dep = deps} a b c d p})
        sc = (CVQuadrant c {cSub {dep = deps} a b c d p})
        sd = (CVQuadrant d {dSub {dep = deps} a b c d p})
