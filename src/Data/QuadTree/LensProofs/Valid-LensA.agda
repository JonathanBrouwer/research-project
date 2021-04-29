{-# OPTIONS --show-implicit --show-irrelevant #-}
module Data.QuadTree.LensProofs.Valid-LensA where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.QuadTree.Lens
open import Data.QuadTree.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive
open import Data.QuadTree.LensProofs.LensLaws
open import Data.QuadTree.LensProofs.LensPostulates
open import Data.QuadTree.LensProofs.LensComposition

--- Lens laws for lensA

ValidLens-LensA-ViewSet : 
    {t : Set} {{eqT : Eq t}} {dep : Nat}
    -> ViewSet (lensA {t} {dep})
ValidLens-LensA-ViewSet (CVQuadrant (Leaf x) {p1}) (CVQuadrant (Leaf v) {p2}) =
    begin
        view lensA (set lensA (CVQuadrant (Leaf x) {p1}) (CVQuadrant (Leaf v) {p2}))
    =⟨⟩
        getConst
            (lensA CConst
            (ifc (x == v && v == v && v == v) 
                then CVQuadrant (Leaf x) 
                else CVQuadrant (Node (Leaf x) (Leaf v) (Leaf v) (Leaf v))))
    =⟨ sym (propFnIfc (x == v && v == v && v == v) (λ x -> getConst (lensA CConst x))) ⟩
        (ifc (x == v && v == v && v == v)   
        then (CVQuadrant (Leaf x))
        else (CVQuadrant (Leaf x)))
    =⟨ propIfcBranchesSame {c = (x == v && v == v && v == v)} (CVQuadrant (Leaf x)) ⟩
         (CVQuadrant (Leaf x))
    end
ValidLens-LensA-ViewSet (CVQuadrant (Node a b c d)) (CVQuadrant (Leaf v)) = refl
ValidLens-LensA-ViewSet (CVQuadrant (Leaf x) {p1}) (CVQuadrant (Node a b@(Leaf vb) c@(Leaf vc) d@(Leaf vd)) {p2}) =    
    begin
        view lensA (set lensA (CVQuadrant (Leaf x) {p1}) (CVQuadrant (Node a b c d) {p2}))
    =⟨⟩
        getConst (lensA CConst (
            ifc (x == vb && vb == vc && vc == vd)
            then (CVQuadrant (Leaf x))
            else (CVQuadrant (Node (Leaf x) (Leaf vb) (Leaf vc) (Leaf vd))) 
        ))
    =⟨ sym (propFnIfc (x == vb && vb == vc && vc == vd) (λ x -> getConst (lensA CConst x))) ⟩
        (ifc (x == vb && vb == vc && vc == vd)  
        then (CVQuadrant (Leaf x))
        else (CVQuadrant (Leaf x)))
    =⟨ propIfcBranchesSame {c = (x == vb && vb == vc && vc == vd)} (CVQuadrant (Leaf x)) ⟩
        (CVQuadrant (Leaf x))
    end
ValidLens-LensA-ViewSet (CVQuadrant (Leaf x)) (CVQuadrant (Node a (Leaf x₁) (Leaf x₂) (Node d d₁ d₂ d₃))) = refl
ValidLens-LensA-ViewSet (CVQuadrant (Leaf x)) (CVQuadrant (Node a (Leaf x₁) (Node c c₁ c₂ c₃) d)) = refl
ValidLens-LensA-ViewSet (CVQuadrant (Leaf x)) (CVQuadrant (Node a (Node b b₁ b₂ b₃) c d)) = refl
ValidLens-LensA-ViewSet (CVQuadrant (Node toa tob toc tod)) (CVQuadrant (Node a b c d)) = refl

ValidLens-LensA-SetView : 
    {t : Set} {{eqT : Eq t}} {dep : Nat}
    -> SetView (lensA {t} {dep})
ValidLens-LensA-SetView {t} {dep} qd@(CVQuadrant (Leaf x) {p}) =
    begin
        set lensA (view lensA qd) qd
    =⟨⟩
        ((ifc (x == x && x == x && x == x) 
            then (CVQuadrant (Leaf x)) 
            else λ {{z}} -> (CVQuadrant (Node (Leaf x) (Leaf x) (Leaf x) (Leaf x)))))
    =⟨ ifcTrue (x == x && x == x && x == x) (andCombine (eqReflexivity x) (andCombine (eqReflexivity x) (eqReflexivity x))) ⟩
        CVQuadrant (Leaf x)
    end
ValidLens-LensA-SetView {t} {dep} cv@(CVQuadrant qd@(Node (Leaf a) (Leaf b) (Leaf c) (Leaf d)) {p}) =
    begin
        set lensA (view lensA cv) cv
    =⟨⟩
        (ifc (a == b && b == c && c == d) then (CVQuadrant (Leaf a)) else (CVQuadrant (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d))))
    =⟨ ifcFalse (a == b && b == c && c == d) (notTrueToFalse (andSnd {depth qd <= S dep} {isCompressed qd} p)) ⟩
        (CVQuadrant (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d)))
    end
ValidLens-LensA-SetView (CVQuadrant (Node (Leaf x) (Leaf x₁) (Leaf x₂) (Node qd₃ qd₄ qd₅ qd₆))) = refl
ValidLens-LensA-SetView (CVQuadrant (Node (Leaf x) (Leaf x₁) (Node qd₂ qd₄ qd₅ qd₆) qd₃)) = refl
ValidLens-LensA-SetView (CVQuadrant (Node (Leaf x) (Node qd₁ qd₄ qd₅ qd₆) qd₂ qd₃)) = refl
ValidLens-LensA-SetView (CVQuadrant (Node (Node qd qd₄ qd₅ qd₆) qd₁ qd₂ qd₃)) = refl    

ValidLens-LensA-SetSet-Lemma : {t : Set} {{eqT : Eq t}} {dep : Nat}
    -> (x a b c d : VQuadrant t {dep}) 
    -> set lensA x (combine a b c d) ≡ (combine x b c d)
ValidLens-LensA-SetSet-Lemma {t} {dep} (CVQuadrant x@(Leaf xv)) (CVQuadrant a@(Leaf va)) (CVQuadrant b@(Leaf vb)) (CVQuadrant c@(Leaf vc)) (CVQuadrant d@(Leaf vd)) =
    begin
        (runIdentity (lensA (λ _ → CIdentity (CVQuadrant (Leaf xv)))
            (ifc va == vb && vb == vc && vc == vd
            then CVQuadrant (Leaf va)
            else CVQuadrant (Node (Leaf va) (Leaf vb) (Leaf vc) (Leaf vd)))))
    =⟨ sym $ propFnIfc (va == vb && vb == vc && vc == vd) (λ g -> (runIdentity (lensA (λ _ → CIdentity (CVQuadrant (Leaf xv) {andCombine (zeroLteAny dep) IsTrue.itsTrue})) g ) ) ) ⟩
        (ifc va == vb && vb == vc && vc == vd
            then ifc xv == va && va == va && va == va
                then CVQuadrant (Leaf xv) 
                else CVQuadrant (Node (Leaf xv) (Leaf va) (Leaf va) (Leaf va))
            else ifc xv == vb && vb == vc && vc == vd
                then CVQuadrant (Leaf xv) 
                else CVQuadrant (Node (Leaf xv) (Leaf vb) (Leaf vc) (Leaf vd)))
    =⟨ ifcTrueMap {c = va == vb && vb == vc && vc == vd} 
            (λ p -> cong 
                (λ q -> ifc xv == q && q == q && q == q 
                    then CVQuadrant (Leaf xv) {andCombine (zeroLteAny (S dep)) IsTrue.itsTrue} 
                    else (λ {{p}} -> CVQuadrant (Node (Leaf xv) (Leaf q) (Leaf q) (Leaf q)) {andCombine (zeroLteAny (dep)) (falseToNotTrue p)}) ) 
                (eqToEquiv va vb (andFst {va == vb} p))  ) ⟩
                
        (ifc va == vb && vb == vc && vc == vd
            then ifc xv == vb && vb == vb && vb == vb
                then CVQuadrant (Leaf xv) {andCombine (zeroLteAny (S dep)) IsTrue.itsTrue}
                else (λ {{p}} -> CVQuadrant (Node (Leaf xv) (Leaf vb) (Leaf vb) (Leaf vb)) {andCombine (zeroLteAny (dep)) (falseToNotTrue p)})
            else ifc xv == vb && vb == vc && vc == vd
                then CVQuadrant (Leaf xv) 
                else CVQuadrant (Node (Leaf xv) (Leaf vb) (Leaf vc) (Leaf vd)))
    =⟨ ifcTrueMap {c = va == vb && vb == vc && vc == vd} 
            (λ p -> cong 
                (λ q -> ifc xv == vb && vb == q && q == q 
                    then CVQuadrant (Leaf xv) {andCombine (zeroLteAny (S dep)) IsTrue.itsTrue} 
                    else (λ {{p}} -> CVQuadrant (Node (Leaf xv) (Leaf vb) (Leaf q) (Leaf q)) {andCombine (zeroLteAny (dep)) (falseToNotTrue p)}) ) 
                (eqToEquiv vb vc (andFst $ andSnd {va == vb} p))  ) ⟩

        (ifc va == vb && vb == vc && vc == vd
            then ifc xv == vb && vb == vc && vc == vc
                then CVQuadrant (Leaf xv) {andCombine (zeroLteAny (S dep)) IsTrue.itsTrue}
                else (λ {{p}} -> CVQuadrant (Node (Leaf xv) (Leaf vb) (Leaf vc) (Leaf vc)) {andCombine (zeroLteAny (dep)) (falseToNotTrue p)})
            else ifc xv == vb && vb == vc && vc == vd
                then CVQuadrant (Leaf xv) 
                else CVQuadrant (Node (Leaf xv) (Leaf vb) (Leaf vc) (Leaf vd)))
    =⟨ ifcTrueMap {c = va == vb && vb == vc && vc == vd} 
            (λ p -> cong 
                (λ q -> ifc xv == vb && vb == vc && vc == q 
                    then CVQuadrant (Leaf xv) {andCombine (zeroLteAny (S dep)) IsTrue.itsTrue} 
                    else (λ {{p}} -> CVQuadrant (Node (Leaf xv) (Leaf vb) (Leaf vc) (Leaf q)) {andCombine (zeroLteAny (dep)) (falseToNotTrue p)}) ) 
                (eqToEquiv vc vd (andSnd $ andSnd {va == vb} p))  ) ⟩

        (ifc va == vb && vb == vc && vc == vd
            then ifc xv == vb && vb == vc && vc == vd
                then CVQuadrant (Leaf xv) {andCombine (zeroLteAny (S dep)) IsTrue.itsTrue}
                else (λ {{p}} -> CVQuadrant (Node (Leaf xv) (Leaf vb) (Leaf vc) (Leaf vd)) {andCombine (zeroLteAny (dep)) (falseToNotTrue p)})
            else ifc xv == vb && vb == vc && vc == vd
                then CVQuadrant (Leaf xv) 
                else CVQuadrant (Node (Leaf xv) (Leaf vb) (Leaf vc) (Leaf vd)))
    =⟨ propIfcBranchesSame {c = va == vb && vb == vc && vc == vd} 
        (ifc xv == vb && vb == vc && vc == vd then CVQuadrant (Leaf xv) else CVQuadrant (Node (Leaf xv) (Leaf vb) (Leaf vc) (Leaf vd))) ⟩

        (ifc xv == vb && vb == vc && vc == vd
            then CVQuadrant (Leaf xv) 
            else CVQuadrant (Node (Leaf xv) (Leaf vb) (Leaf vc) (Leaf vd)))
    end
ValidLens-LensA-SetSet-Lemma {t} {dep} cvx@(CVQuadrant x@(Node x1 x2 x3 x4) {p}) cva@(CVQuadrant a@(Leaf va)) cvb@(CVQuadrant b@(Leaf vb)) cvc@(CVQuadrant c@(Leaf vc)) cvd@(CVQuadrant d@(Leaf vd)) =
    begin
        runIdentity (lensA (λ _ → CIdentity cvx)
            (ifc va == vb && vb == vc && vc == vd
            then CVQuadrant (Leaf va) 
            else CVQuadrant (Node (Leaf va) (Leaf vb) (Leaf vc) (Leaf vd))))
    =⟨ sym $ propFnIfc (va == vb && vb == vc && vc == vd) (λ g -> (runIdentity (lensA (λ _ → CIdentity cvx) g ) ) ) ⟩
        (ifc va == vb && vb == vc && vc == vd
        then CVQuadrant (Node x (Leaf va) (Leaf va) (Leaf va))
        else CVQuadrant (Node x (Leaf vb) (Leaf vc) (Leaf vd)))
    =⟨ ifcTrueMap {c = va == vb && vb == vc && vc == vd} (λ p -> cong (λ q -> combine cvx (cvq q) (cvq q) (cvq q)) (eqToEquiv va vb (andFst {va == vb} p)))   ⟩
        (ifc va == vb && vb == vc && vc == vd
        then CVQuadrant (Node x (Leaf vb) (Leaf vb) (Leaf vb))
        else CVQuadrant (Node x (Leaf vb) (Leaf vc) (Leaf vd)))
    =⟨ ifcTrueMap {c = va == vb && vb == vc && vc == vd} (λ p -> cong (λ q -> combine cvx cvb (cvq q) (cvq q)) (eqToEquiv vb vc (andFst $ andSnd {va == vb} p)))   ⟩
        (ifc va == vb && vb == vc && vc == vd
        then CVQuadrant (Node x (Leaf vb) (Leaf vc) (Leaf vc))
        else CVQuadrant (Node x (Leaf vb) (Leaf vc) (Leaf vd)))
    =⟨ ifcTrueMap {c = va == vb && vb == vc && vc == vd} (λ p -> cong (λ q -> combine cvx cvb cvc (cvq q)) (eqToEquiv vc vd (andSnd $ andSnd {va == vb} p)))   ⟩
        (ifc va == vb && vb == vc && vc == vd
        then CVQuadrant (Node x (Leaf vb) (Leaf vc) (Leaf vd))
        else CVQuadrant (Node x (Leaf vb) (Leaf vc) (Leaf vd)))
    =⟨ propIfcBranchesSame {c = va == vb && vb == vc && vc == vd} (CVQuadrant (Node x (Leaf vb) (Leaf vc) (Leaf vd))) ⟩
        CVQuadrant (Node x (Leaf vb) (Leaf vc) (Leaf vd))
    end where
        -- Construct a valid leaf from a value
        cvq : t -> VQuadrant t {dep}
        cvq q = CVQuadrant (Leaf q) {andCombine (zeroLteAny dep) IsTrue.itsTrue}
ValidLens-LensA-SetSet-Lemma (CVQuadrant _) (CVQuadrant (Leaf _)) (CVQuadrant (Leaf _)) (CVQuadrant (Leaf _)) (CVQuadrant (Node _ _ _ _)) = refl
ValidLens-LensA-SetSet-Lemma (CVQuadrant _) (CVQuadrant (Leaf _)) (CVQuadrant (Leaf _)) (CVQuadrant (Node _ _ _ _)) (CVQuadrant _) = refl
ValidLens-LensA-SetSet-Lemma (CVQuadrant _) (CVQuadrant (Leaf _)) (CVQuadrant (Node _ _ _ _)) (CVQuadrant _) (CVQuadrant _) = refl
ValidLens-LensA-SetSet-Lemma (CVQuadrant _) (CVQuadrant (Node _ _ _ _)) (CVQuadrant _) (CVQuadrant _) (CVQuadrant _) = refl

ValidLens-LensA-SetSet : 
    {t : Set} {{eqT : Eq t}} {dep : Nat}
    -> SetSet (lensA {t} {dep})
ValidLens-LensA-SetSet a@(CVQuadrant qda) b@(CVQuadrant qdb) x@(CVQuadrant qdx@(Leaf xv)) =
    begin
        set lensA (CVQuadrant qdb) (combine (CVQuadrant qda) (CVQuadrant (Leaf xv)) (CVQuadrant (Leaf xv)) (CVQuadrant (Leaf xv)))
    =⟨ ValidLens-LensA-SetSet-Lemma (CVQuadrant qdb) (CVQuadrant qda) (CVQuadrant (Leaf xv)) (CVQuadrant (Leaf xv)) (CVQuadrant (Leaf xv)) ⟩
        combine (CVQuadrant qdb) (CVQuadrant (Leaf xv)) (CVQuadrant (Leaf xv)) (CVQuadrant (Leaf xv))
    end
ValidLens-LensA-SetSet (CVQuadrant qda) (CVQuadrant qdb) (CVQuadrant qdx@(Node xa xb xc xd)) =
    begin
        set lensA (CVQuadrant qdb) (combine (CVQuadrant qda) (CVQuadrant xb) (CVQuadrant xc) (CVQuadrant xd))
    =⟨ ValidLens-LensA-SetSet-Lemma (CVQuadrant qdb) (CVQuadrant qda) (CVQuadrant xb) (CVQuadrant xc) (CVQuadrant xd) ⟩
        combine (CVQuadrant qdb) (CVQuadrant xb) (CVQuadrant xc) (CVQuadrant xd)
    end

ValidLens-LensA : {t : Set} {{eqT : Eq t}} {dep : Nat}
    -> ValidLens (VQuadrant t {S dep}) (VQuadrant t {dep})
ValidLens-LensA = CValidLens lensA (ValidLens-LensA-ViewSet) (ValidLens-LensA-SetView) (ValidLens-LensA-SetSet)