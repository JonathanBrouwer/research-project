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

-- ValidLens-LensA-SetSet : 
--     {t : Set} {{eqT : Eq t}}
--     -> SetSet (lensA {t})
-- ValidLens-LensA-SetSet (Leaf va) (Leaf vb) (Leaf x) =
--     begin
--         set lensA (Leaf vb) (set lensA (Leaf va) (Leaf x))
--     =⟨⟩
--         runIdentity 
--             (lensA (λ _ → CIdentity (Leaf vb))
--                 (if va == x && x == x && x == x 
--                     then Leaf va 
--                     else Node (Leaf va) (Leaf x) (Leaf x) (Leaf x)
--                 ))
--     =⟨ sym $ propFnIf {c = (va == x && x == x && x == x)} (λ g -> runIdentity (lensA (λ _ → CIdentity (Leaf vb)) g )) ⟩
--         (if va == x && x == x && x == x 
--             then runIdentity 
--                 (lensA (λ _ → CIdentity (Leaf vb))  (Leaf va) )
--             else runIdentity 
--                 (lensA (λ _ → CIdentity (Leaf vb))  (Node (Leaf va) (Leaf x) (Leaf x) (Leaf x))  )
--         )
--     =⟨⟩
--         (if va == x && x == x && x == x 
--             then if vb == va && va == va && va == va then Leaf vb else Node (Leaf vb) (Leaf va) (Leaf va) (Leaf va)
--             else (if vb == x && x == x && x == x then Leaf vb else Node (Leaf vb) (Leaf x) (Leaf x) (Leaf x))
--         )
--     =⟨ ifTrueMap {c = va == x && x == x && x == x} 
--         (λ p -> cong ((λ q -> if vb == q && q == q && q == q then Leaf vb else Node (Leaf vb) (Leaf q) (Leaf q) (Leaf q))) 
--         (eqToEquiv va x (andFst {va == x} p))) ⟩
--         (if va == x && x == x && x == x 
--             then if vb == x && x == x && x == x then Leaf vb else Node (Leaf vb) (Leaf x) (Leaf x) (Leaf x)
--             else if vb == x && x == x && x == x then Leaf vb else Node (Leaf vb) (Leaf x) (Leaf x) (Leaf x)
--         )
--     =⟨ propIfBranchesSame {c = va == x && x == x && x == x} (if vb == x && x == x && x == x then Leaf vb else Node (Leaf vb) (Leaf x) (Leaf x) (Leaf x)) ⟩
--         (if vb == x && x == x && x == x then Leaf vb else Node (Leaf vb) (Leaf x) (Leaf x) (Leaf x))
--     end
-- ValidLens-LensA-SetSet (Leaf va) (Node b1 b2 b3 b4) (Leaf x) =
--     begin
--         set lensA (Node b1 b2 b3 b4) (set lensA (Leaf va) (Leaf x))
--     =⟨⟩
--         runIdentity (lensA (λ _ → CIdentity (Node b1 b2 b3 b4)) (
--             if va == x && x == x && x == x 
--             then Leaf va 
--             else Node (Leaf va) (Leaf x) (Leaf x) (Leaf x)
--         ))
--     =⟨ sym $ propFnIf {c = va == x && x == x && x == x } (λ g -> runIdentity (lensA (λ _ → CIdentity (Node b1 b2 b3 b4)) (g)) ) ⟩
--         (if va == x && x == x && x == x 
--         then runIdentity (lensA (λ _ → CIdentity (Node b1 b2 b3 b4)) (Leaf va))
--         else runIdentity (lensA (λ _ → CIdentity (Node b1 b2 b3 b4)) (Node (Leaf va) (Leaf x) (Leaf x) (Leaf x))))
--     =⟨⟩
--         (if va == x && x == x && x == x 
--         then Node (Node b1 b2 b3 b4) (Leaf va) (Leaf va) (Leaf va)
--         else Node (Node b1 b2 b3 b4) (Leaf x) (Leaf x) (Leaf x))
--     =⟨ ifTrueMap {c = va == x && x == x && x == x} 
--         (λ p -> cong ((λ q -> Node (Node b1 b2 b3 b4) (Leaf q) (Leaf q) (Leaf q) )) 
--         (eqToEquiv va x (andFst {va == x} p))) ⟩
--         (if va == x && x == x && x == x 
--         then Node (Node b1 b2 b3 b4) (Leaf x) (Leaf x) (Leaf x)
--         else Node (Node b1 b2 b3 b4) (Leaf x) (Leaf x) (Leaf x))
--     =⟨ propIfBranchesSame (Node (Node b1 b2 b3 b4) (Leaf x) (Leaf x) (Leaf x)) ⟩
--         set lensA (Node b1 b2 b3 b4) (Leaf x)
--     end
-- ValidLens-LensA-SetSet (Leaf va) (Leaf vb) (Node xa (Leaf x) (Leaf x₁) (Node xd xd₁ xd₂ xd₃)) = refl
-- ValidLens-LensA-SetSet (Leaf va) (Leaf vb) (Node xa (Leaf x) (Node xc xc₁ xc₂ xc₃) xd) = refl
-- ValidLens-LensA-SetSet (Leaf va) (Leaf vb) (Node xa (Node xb xb₁ xb₂ xb₃) xc xd) = refl
-- ValidLens-LensA-SetSet (Leaf va) (Leaf vb) (Node xa (Leaf xvb) (Leaf xvc) (Leaf xvd)) =
--     begin
--         set lensA (Leaf vb) (set lensA (Leaf va) (Node xa (Leaf xvb) (Leaf xvc) (Leaf xvd)))
--     =⟨⟩
--         runIdentity (lensA (λ _ → CIdentity (Leaf vb))
--             (if va == xvb && xvb == xvc && xvc == xvd
--             then Leaf va 
--             else Node (Leaf va) (Leaf xvb) (Leaf xvc) (Leaf xvd)))
--     =⟨ sym $ propFnIf {c = va == xvb && xvb == xvc && xvc == xvd } ((λ g -> runIdentity (lensA (λ _ → CIdentity (Leaf vb)) g))) ⟩
--         (if va == xvb && xvb == xvc && xvc == xvd
--         then (runIdentity (lensA (λ _ → CIdentity (Leaf vb)) (Leaf va)))
--         else (runIdentity (lensA (λ _ → CIdentity (Leaf vb)) (Node (Leaf va) (Leaf xvb) (Leaf xvc) (Leaf xvd)))))
--     =⟨⟩
--         (if va == xvb && xvb == xvc && xvc == xvd
--         then (if vb == va && va == va && va == va then Leaf vb else Node (Leaf vb) (Leaf va) (Leaf va) (Leaf va)          )
--         else (if vb == xvb && xvb == xvc && xvc == xvd then Leaf vb else Node (Leaf vb) (Leaf xvb) (Leaf xvc) (Leaf xvd)) )
--     =⟨ ifTrueMap {c = va == xvb && xvb == xvc && xvc == xvd} 
--         (λ p -> cong ((λ q -> if vb == q && q == q && q == q then Leaf vb else Node (Leaf vb) (Leaf q) (Leaf q) (Leaf q) )) 
--         (eqToEquiv va xvb (andFst {va == xvb} p))) ⟩
--             (if va == xvb && xvb == xvc && xvc == xvd
--             then (if vb == xvb && xvb == xvb && xvb == xvb then Leaf vb else Node (Leaf vb) (Leaf xvb) (Leaf xvb) (Leaf xvb)  ) 
--             else (if vb == xvb && xvb == xvc && xvc == xvd then Leaf vb else Node (Leaf vb) (Leaf xvb) (Leaf xvc) (Leaf xvd)) )
--     =⟨ ifTrueMap {c = va == xvb && xvb == xvc && xvc == xvd} 
--         (λ p -> cong ((λ q -> if vb == xvb && xvb == q && q == q then Leaf vb else Node (Leaf vb) (Leaf xvb) (Leaf q) (Leaf q) )) 
--         (eqToEquiv xvb xvc (andFst $ andSnd {va == xvb} p))) ⟩
--             (if va == xvb && xvb == xvc && xvc == xvd
--             then (if vb == xvb && xvb == xvc && xvc == xvc then Leaf vb else Node (Leaf vb) (Leaf xvb) (Leaf xvc) (Leaf xvc)  ) 
--             else (if vb == xvb && xvb == xvc && xvc == xvd then Leaf vb else Node (Leaf vb) (Leaf xvb) (Leaf xvc) (Leaf xvd)) )
--     =⟨ ifTrueMap {c = va == xvb && xvb == xvc && xvc == xvd} 
--         (λ p -> cong ((λ q -> if vb == xvb && xvb == xvc && xvc == q then Leaf vb else Node (Leaf vb) (Leaf xvb) (Leaf xvc) (Leaf q) )) 
--         (eqToEquiv xvc xvd (andSnd $ andSnd {va == xvb} p))) ⟩
--             (if va == xvb && xvb == xvc && xvc == xvd
--             then (if vb == xvb && xvb == xvc && xvc == xvd then Leaf vb else Node (Leaf vb) (Leaf xvb) (Leaf xvc) (Leaf xvd)  ) 
--             else (if vb == xvb && xvb == xvc && xvc == xvd then Leaf vb else Node (Leaf vb) (Leaf xvb) (Leaf xvc) (Leaf xvd)) )
--     =⟨ propIfBranchesSame {c = va == xvb && xvb == xvc && xvc == xvd} (if vb == xvb && xvb == xvc && xvc == xvd then Leaf vb else Node (Leaf vb) (Leaf xvb) (Leaf xvc) (Leaf xvd)  ) ⟩
--         (if vb == xvb && xvb == xvc && xvc == xvd then Leaf vb else Node (Leaf vb) (Leaf xvb) (Leaf xvc) (Leaf xvd))
--     =⟨⟩
--         set lensA (Leaf vb) (Node xa (Leaf xvb) (Leaf xvc) (Leaf xvd))
--     end
-- ValidLens-LensA-SetSet (Leaf va) (Node b1 b2 b3 b4) (Node xa (Leaf xvb) (Leaf xvc) (Leaf xvd)) =
--     begin
--         set lensA (Node b1 b2 b3 b4) (set lensA (Leaf va) (Node xa (Leaf xvb) (Leaf xvc) (Leaf xvd)))
--     =⟨⟩
--         runIdentity (lensA (λ _ → CIdentity (Node b1 b2 b3 b4))
--             (if va == xvb && xvb == xvc && xvc == xvd
--             then Leaf va 
--             else Node (Leaf va) (Leaf xvb) (Leaf xvc) (Leaf xvd)))
--     =⟨ sym $ propFnIf {c = va == xvb && xvb == xvc && xvc == xvd} (λ g -> runIdentity (lensA (λ _ → CIdentity (Node b1 b2 b3 b4)) g ) )   ⟩
--         (if va == xvb && xvb == xvc && xvc == xvd
--         then runIdentity (lensA (λ _ → CIdentity (Node b1 b2 b3 b4)) (Leaf va))
--         else runIdentity (lensA (λ _ → CIdentity (Node b1 b2 b3 b4)) (Node (Leaf va) (Leaf xvb) (Leaf xvc) (Leaf xvd))))
--     =⟨⟩
--         (if va == xvb && xvb == xvc && xvc == xvd
--         then Node (Node b1 b2 b3 b4) (Leaf va) (Leaf va) (Leaf va)
--         else Node (Node b1 b2 b3 b4) (Leaf xvb) (Leaf xvc) (Leaf xvd))
--     =⟨ ifTrueMap {c = va == xvb && xvb == xvc && xvc == xvd} (λ p -> cong (λ q -> Node (Node b1 b2 b3 b4) (Leaf q) (Leaf q) (Leaf q)) (eqToEquiv va xvb (andFst {va == xvb} p)))   ⟩
--         (if va == xvb && xvb == xvc && xvc == xvd
--         then Node (Node b1 b2 b3 b4) (Leaf xvb) (Leaf xvb) (Leaf xvb)
--         else Node (Node b1 b2 b3 b4) (Leaf xvb) (Leaf xvc) (Leaf xvd))
--     =⟨ ifTrueMap {c = va == xvb && xvb == xvc && xvc == xvd} (λ p -> cong (λ q -> Node (Node b1 b2 b3 b4) (Leaf xvb) (Leaf q) (Leaf q)) (eqToEquiv xvb xvc (andFst $ andSnd {va == xvb} p)))   ⟩
--         (if va == xvb && xvb == xvc && xvc == xvd
--         then Node (Node b1 b2 b3 b4) (Leaf xvb) (Leaf xvc) (Leaf xvc)
--         else Node (Node b1 b2 b3 b4) (Leaf xvb) (Leaf xvc) (Leaf xvd))
--     =⟨ ifTrueMap {c = va == xvb && xvb == xvc && xvc == xvd} (λ p -> cong (λ q -> Node (Node b1 b2 b3 b4) (Leaf xvb) (Leaf xvc) (Leaf q)) (eqToEquiv xvc xvd (andSnd $ andSnd {va == xvb} p)))   ⟩
--         (if va == xvb && xvb == xvc && xvc == xvd
--         then Node (Node b1 b2 b3 b4) (Leaf xvb) (Leaf xvc) (Leaf xvd)
--         else Node (Node b1 b2 b3 b4) (Leaf xvb) (Leaf xvc) (Leaf xvd))
--     =⟨ propIfBranchesSame {c = va == xvb && xvb == xvc && xvc == xvd} (Node (Node b1 b2 b3 b4) (Leaf xvb) (Leaf xvc) (Leaf xvd)) ⟩
--         Node (Node b1 b2 b3 b4) (Leaf xvb) (Leaf xvc) (Leaf xvd)
--     =⟨⟩
--         set lensA (Node b1 b2 b3 b4) (Node xa (Leaf xvb) (Leaf xvc) (Leaf xvd))
--     end
-- ValidLens-LensA-SetSet (Leaf va) (Node b1 b2 b3 b4) (Node xa (Leaf x) (Leaf x₁) (Node xd xd₁ xd₂ xd₃)) = refl
-- ValidLens-LensA-SetSet (Leaf va) (Node b1 b2 b3 b4) (Node xa (Leaf x) (Node xc xc₁ xc₂ xc₃) xd) = refl
-- ValidLens-LensA-SetSet (Leaf va) (Node b1 b2 b3 b4) (Node xa (Node xb xb₁ xb₂ xb₃) xc xd) = refl
-- ValidLens-LensA-SetSet (Node a1 a2 a3 a4) (Leaf b) (Leaf x) = refl
-- ValidLens-LensA-SetSet (Node a1 a2 a3 a4) (Leaf b) (Node x1 x2 x3 x4) = refl
-- ValidLens-LensA-SetSet (Node a1 a2 a3 a4) (Node b1 b2 b3 b4) (Leaf x) = refl
-- ValidLens-LensA-SetSet (Node a1 a2 a3 a4) (Node b1 b2 b3 b4) (Node x1 x2 x3 x4) = refl

-- ValidLens-LensA : {t : Set} {{eqT : Eq t}}
--     -> ValidLens (Quadrant t) (Quadrant t)
-- ValidLens-LensA = CValidLens lensA (ValidLens-LensA-ViewSet) (ValidLens-LensA-SetView) (ValidLens-LensA-SetSet)