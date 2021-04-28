module Data.QuadTree.LensLaws where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.QuadTree.Lens
open import Data.QuadTree.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive


---- Generic lens laws

ViewSet : {a b : Set} -> (l : CLens a b) -> Set
ViewSet {a} {b} l = (v : b) (s : a) -> view l (set l v s) ≡ v

SetView : {a b : Set} -> (l : CLens a b) -> Set
SetView {a} {b} l = (s : a) -> set l (view l s) s ≡ s

SetSet : {a b : Set} -> (l : CLens a b) -> Set
SetSet {a} {b} l = (v1 v2 : b) (s : a) -> set l v2 (set l v1 s) ≡ set l v2 s

data ValidLens (a b : Set) : Set₁ where
  CValidLens : (l : CLens a b) -> ViewSet l -> SetView l -> SetSet l -> ValidLens a b

toLens : ValidLens a b -> CLens a b
toLens (CValidLens l _ _ _) = l

---- Lens postulates
-- These are provable using the isomorphism to the getter+setter style

postulate 
    prop-view-compose : {a b c : Set} 
        -> (l1 : ValidLens a b)
        -> (l2 : ValidLens b c)
        -> (v : a)
        -> (view ((toLens l1) ∘ (toLens l2))) v ≡ (view (toLens l2) ∘ view (toLens l1)) v
    prop-set-compose : {a b c : Set} 
        -> (l1 : ValidLens a b)
        -> (l2 : ValidLens b c)
        -> (v : a) (t : c)
        -> (set ((toLens l1) ∘ (toLens l2))) t v ≡ over (toLens l1) (set (toLens l2) t) v
    prop-over-is-setget : {a b : Set} 
        -> (l : ValidLens a b)
        -> (f : b -> b) (v : a)
        -> over (toLens l) f v ≡ set (toLens l) (f (view (toLens l) v)) v

prop-set-compose-dir : {a b c : Set} 
    -> (l1 : ValidLens a b)
    -> (l2 : ValidLens b c)
    -> (v : a) (t : c)
    -> (set ((toLens l1) ∘ (toLens l2))) t v ≡ set (toLens l1) ((set (toLens l2) t) (view (toLens l1) v)) v
prop-set-compose-dir vl1@(CValidLens l1 vs1 sv1 ss1) vl2@(CValidLens l2 vs2 sv2 ss2) v t =
    begin
        set (l1 ∘ l2) t v
    =⟨ prop-set-compose vl1 vl2 v t ⟩
        over l1 (set l2 t) v
    =⟨ prop-over-is-setget vl1 (set l2 t) v ⟩
        set l1 ((set l2 t) (view l1 v)) v
    end

--- Proving the composition of Valid Lenses
prop-Composition-ViewSet : {a b c : Set} 
    -> (l1 : ValidLens a b)
    -> (l2 : ValidLens b c)
    -> ViewSet ((toLens l1) ∘ (toLens l2))
prop-Composition-ViewSet {a} {b} {c} vl1@(CValidLens l1 vs1 sv1 ss1) vl2@(CValidLens l2 vs2 sv2 ss2) v s = 
    begin 
        view (l1 ∘ l2) (set (l1 ∘ l2) v s) 
    =⟨ prop-view-compose vl1 vl2 (set (l1 ∘ l2) v s) ⟩
        view l2 ( view l1 (set (l1 ∘ l2) v s))
    =⟨ cong (view l2 ∘ view l1) (prop-set-compose-dir vl1 vl2 s v) ⟩
        view l2 ( view l1 (set l1 ((set l2 v) (view l1 s)) s))
    =⟨ cong (view l2) (vs1 ((set l2 v) (view l1 s)) s) ⟩
        view l2 (set l2 v (view l1 s))
    =⟨ vs2 v (view l1 s) ⟩
        v 
    end

prop-Composition-SetView : {a b c : Set} 
    -> (l1 : ValidLens a b)
    -> (l2 : ValidLens b c)
    -> SetView ((toLens l1) ∘ (toLens l2))
prop-Composition-SetView {a} {b} {c} vl1@(CValidLens l1 vs1 sv1 ss1) vl2@(CValidLens l2 vs2 sv2 ss2) s = 
    begin 
        set (l1 ∘ l2) (view (l1 ∘ l2) s) s
    =⟨ cong (λ x -> set (l1 ∘ l2) x s) (prop-view-compose vl1 vl2 s) ⟩
        set (l1 ∘ l2) (view l2 (view l1 s)) s 
    =⟨ prop-set-compose-dir vl1 vl2 s (view l2 (view l1 s)) ⟩
        set l1 (set l2 (view l2 (view l1 s)) (view l1 s)) s
    =⟨ cong (λ x -> set l1 x s) (sv2 (view l1 s)) ⟩
        set l1 (view l1 s) s
    =⟨ sv1 s ⟩
        s 
    end

prop-Composition-SetSet : {a b c : Set} 
    -> (l1 : ValidLens a b)
    -> (l2 : ValidLens b c)
    -> SetSet ((toLens l1) ∘ (toLens l2))
prop-Composition-SetSet {a} {b} {c} vl1@(CValidLens l1 vs1 sv1 ss1) vl2@(CValidLens l2 vs2 sv2 ss2) v1 v2 s =
    begin 
        set (l1 ∘ l2) v2 (set (l1 ∘ l2) v1 s)
    =⟨ cong (set (l1 ∘ l2) v2) (prop-set-compose-dir vl1 vl2 s v1) ⟩
        set (l1 ∘ l2) v2 (set l1 (set l2 v1 (view l1 s)) s)
    =⟨ prop-set-compose-dir vl1 vl2 (set l1 ((set l2 v1) (view l1 s)) s) v2 ⟩
        set l1 
            (set l2 
                v2 
                (view l1 
                    (set l1 ((set l2 v1) (view l1 s)) s)
                )
            ) 
            (set l1 (set l2 v1 (view l1 s)) s)
    =⟨ cong (λ x -> set l1 (set l2 v2 x) (set l1 ((set l2 v1) (view l1 s)) s)) (vs1 ((set l2 v1) (view l1 s)) s) ⟩
        set l1 
            (set l2 
                v2 
                (set l2 v1 (view l1 s))
            ) 
            (set l1 (set l2 v1 (view l1 s)) s)
    =⟨ cong (λ x -> set l1 x (set l1 (set l2 v1 (view l1 s)) s)) (ss2 v1 v2 (view l1 s)) ⟩
        set l1 
            (set l2 
                v2 
                (view l1 s)
            ) 
            (set l1 (set l2 v1 (view l1 s)) s)
    =⟨ ss1 ((set l2 v1 (view l1 s))) ((set l2 v2 (view l1 s))) s ⟩
        set l1 
            (set l2 
                v2 
                (view l1 s)
            ) 
            s
    =⟨ sym (prop-set-compose-dir vl1 vl2 s v2) ⟩
        set (l1 ∘ l2) v2 s
    end

composeLens : {a b c : Set} -> (ValidLens a b) -> (ValidLens b c) -> (ValidLens a c)
composeLens vl1@(CValidLens l1 vs1 sv1 ss1) vl2@(CValidLens l2 vs2 sv2 ss2) 
    = CValidLens (l1 ∘ l2) (prop-Composition-ViewSet vl1 vl2) (prop-Composition-SetView vl1 vl2) (prop-Composition-SetSet vl1 vl2)

---- Lens laws for lensWrappedTree

ValidLens-WrappedTree-ViewSet : 
    {t : Set} {{eqT : Eq t}}
    -> ViewSet (lensWrappedTree {t})
ValidLens-WrappedTree-ViewSet qdn (Wrapper qdo (w , h)) = refl

ValidLens-WrappedTree-SetView : 
    {t : Set} {{eqT : Eq t}}
    -> SetView (lensWrappedTree {t})
ValidLens-WrappedTree-SetView (Wrapper qdo (w , h)) = refl

ValidLens-WrappedTree-SetSet : 
    {t : Set} {{eqT : Eq t}}
    -> SetSet (lensWrappedTree {t})
ValidLens-WrappedTree-SetSet qd1 qd2 (Wrapper qdo (w , h)) = refl

ValidLens-WrappedTree :
    {t : Set} {{eqT : Eq t}}
    -> ValidLens (QuadTree t) (Quadrant t)
ValidLens-WrappedTree = CValidLens lensWrappedTree (ValidLens-WrappedTree-ViewSet) (ValidLens-WrappedTree-SetView) (ValidLens-WrappedTree-SetSet)

--- Lens laws for lensLeaf

ValidLens-Leaf-ViewSet : 
    {t : Set} {{eqT : Eq t}}
    -> ViewSet (lensLeaf {t})
ValidLens-Leaf-ViewSet v (Leaf lv) = refl
ValidLens-Leaf-ViewSet v (Node a b c d) = impossible --TODO

ValidLens-Leaf-SetView : 
    {t : Set} {{eqT : Eq t}}
    -> SetView (lensLeaf {t})
ValidLens-Leaf-SetView (Leaf lv) = refl
ValidLens-Leaf-SetView (Node a b c d) = impossible --TODO

ValidLens-Leaf-SetSet : 
    {t : Set} {{eqT : Eq t}}
    -> SetSet (lensLeaf {t})
ValidLens-Leaf-SetSet v1 v2 (Leaf lv) = refl
ValidLens-Leaf-SetSet v1 v2 (Node a b c d) = impossible --TODO

ValidLens-Leaf :
    {t : Set} {{eqT : Eq t}}
    -> ValidLens (Quadrant t) t
ValidLens-Leaf = CValidLens lensLeaf ValidLens-Leaf-ViewSet ValidLens-Leaf-SetView ValidLens-Leaf-SetSet


--- Lens laws for lensA

ValidLens-LensA-ViewSet : 
    {t : Set} {{eqT : Eq t}}
    -> ViewSet (lensA {t})
ValidLens-LensA-ViewSet (Leaf x) (Leaf v) =
    begin
        view lensA (set lensA (Leaf x) (Leaf v))
    =⟨⟩
        getConst (lensA CConst (
            if (x == v && v == v && v == v)   
            then Leaf x 
            else Node (Leaf x) (Leaf v) (Leaf v) (Leaf v)
        ))
    =⟨ sym (propFnIf {c = (x == v && v == v && v == v)} (λ x -> getConst (lensA CConst x))) ⟩
        (if (x == v && v == v && v == v)   
        then (getConst (lensA CConst (Node (Leaf x) (Leaf v) (Leaf v) (Leaf v))))
        else (getConst (lensA CConst (Leaf x))))
    =⟨⟩
        (if (x == v && v == v && v == v)   
        then (Leaf x)
        else (Leaf x))
    =⟨ propIfBranchesSame (Leaf x) ⟩
        (Leaf x)
    end
ValidLens-LensA-ViewSet (Node a b c d) (Leaf v) = refl
ValidLens-LensA-ViewSet (Leaf x) (Node a b@(Leaf vb) c@(Leaf vc) d@(Leaf vd)) =    
    begin
        view lensA (set lensA (Leaf x) (Node a b c d))
    =⟨⟩
        getConst (lensA CConst (
            if (x == vb && vb == vc && vc == vd)
            then Leaf x
            else Node (Leaf x) (Leaf vb) (Leaf vc) (Leaf vd) 
        ))
    =⟨ sym (propFnIf {c = (x == vb && vb == vc && vc == vd)} (λ x -> getConst (lensA CConst x))) ⟩
        (if (x == vb && vb == vc && vc == vd)  
        then (getConst (lensA CConst (Leaf x)))
        else (getConst (lensA CConst (Node (Leaf x) (Leaf vb) (Leaf vc) (Leaf vd)))))
    =⟨⟩
        (if (x == vb && vb == vc && vc == vd)  
        then (Leaf x)
        else (Leaf x))
    =⟨ propIfBranchesSame (Leaf x) ⟩
        (Leaf x)
    end
ValidLens-LensA-ViewSet (Leaf x) (Node a (Leaf x₁) (Leaf x₂) (Node d d₁ d₂ d₃)) = refl
ValidLens-LensA-ViewSet (Leaf x) (Node a (Leaf x₁) (Node c c₁ c₂ c₃) d) = refl
ValidLens-LensA-ViewSet (Leaf x) (Node a (Node b b₁ b₂ b₃) c d) = refl
ValidLens-LensA-ViewSet (Node toa tob toc tod) (Node a b c d) = refl

ValidLens-LensA-SetView : 
    {t : Set} {{eqT : Eq t}}
    -> SetView (lensA {t})
ValidLens-LensA-SetView (Leaf x) =
    begin
        set lensA (view lensA (Leaf x)) (Leaf x)
    =⟨⟩
        (if (x == x && x == x && x == x) then Leaf x else Node (Leaf x) (Leaf x) (Leaf x) (Leaf x))
    =⟨ ifTrue (x == x && x == x && x == x) (andCombine (eqReflexivity x) (andCombine (eqReflexivity x) (eqReflexivity x))) ⟩
        Leaf x
    end
ValidLens-LensA-SetView (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d)) =
    begin
        set lensA (view lensA (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d))) (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d))
    =⟨⟩
        (if (a == b && b == c && c == d) then Leaf a else Node (Leaf a) (Leaf b) (Leaf c) (Leaf d))
    =⟨ ifFalse (a == b && b == c && c == d) compressedProof ⟩
        Node (Leaf a) (Leaf b) (Leaf c) (Leaf d)
    end where
    -- TODO: ONLY TRUE IF INPUT IS COMPRESSED!
    postulate compressedProof : IsFalse (a == b && b == c && c == d)
ValidLens-LensA-SetView (Node (Leaf x) (Leaf x₁) (Leaf x₂) (Node qd₃ qd₄ qd₅ qd₆)) = refl
ValidLens-LensA-SetView (Node (Leaf x) (Leaf x₁) (Node qd₂ qd₄ qd₅ qd₆) qd₃) = refl
ValidLens-LensA-SetView (Node (Leaf x) (Node qd₁ qd₄ qd₅ qd₆) qd₂ qd₃) = refl
ValidLens-LensA-SetView (Node (Node qd qd₄ qd₅ qd₆) qd₁ qd₂ qd₃) = refl    

-- set l v2 (set l v1 s) ≡ set l v2 s
ValidLens-LensA-SetSet : 
    {t : Set} {{eqT : Eq t}}
    -> SetSet (lensA {t})
ValidLens-LensA-SetSet (Leaf va) (Leaf vb) (Leaf x) =
    begin
        set lensA (Leaf vb) (set lensA (Leaf va) (Leaf x))
    =⟨⟩
        runIdentity 
            (lensA (λ _ → CIdentity (Leaf vb))
                (if va == x && x == x && x == x 
                    then Leaf va 
                    else Node (Leaf va) (Leaf x) (Leaf x) (Leaf x)
                ))
    =⟨ sym $ propFnIf {c = (va == x && x == x && x == x)} (λ g -> runIdentity (lensA (λ _ → CIdentity (Leaf vb)) g )) ⟩
        (if va == x && x == x && x == x 
            then runIdentity 
                (lensA (λ _ → CIdentity (Leaf vb))  (Leaf va) )
            else runIdentity 
                (lensA (λ _ → CIdentity (Leaf vb))  (Node (Leaf va) (Leaf x) (Leaf x) (Leaf x))  )
        )
    =⟨⟩
        (if va == x && x == x && x == x 
            then if vb == va && va == va && va == va then Leaf vb else Node (Leaf vb) (Leaf va) (Leaf va) (Leaf va)
            else (if vb == x && x == x && x == x then Leaf vb else Node (Leaf vb) (Leaf x) (Leaf x) (Leaf x))
        )
    =⟨ ifTrueMap {c = va == x && x == x && x == x} 
        (λ p -> cong ((λ q -> if vb == q && q == q && q == q then Leaf vb else Node (Leaf vb) (Leaf q) (Leaf q) (Leaf q))) 
        (eqToEquiv va x (andFst {va == x} p))) ⟩
        (if va == x && x == x && x == x 
            then if vb == x && x == x && x == x then Leaf vb else Node (Leaf vb) (Leaf x) (Leaf x) (Leaf x)
            else if vb == x && x == x && x == x then Leaf vb else Node (Leaf vb) (Leaf x) (Leaf x) (Leaf x)
        )
    =⟨ propIfBranchesSame {c = va == x && x == x && x == x} (if vb == x && x == x && x == x then Leaf vb else Node (Leaf vb) (Leaf x) (Leaf x) (Leaf x)) ⟩
        (if vb == x && x == x && x == x then Leaf vb else Node (Leaf vb) (Leaf x) (Leaf x) (Leaf x))
    end
ValidLens-LensA-SetSet (Leaf va) (Node b1 b2 b3 b4) (Leaf x) =
    begin
        set lensA (Node b1 b2 b3 b4) (set lensA (Leaf va) (Leaf x))
    =⟨⟩
        runIdentity (lensA (λ _ → CIdentity (Node b1 b2 b3 b4)) (
            if va == x && x == x && x == x 
            then Leaf va 
            else Node (Leaf va) (Leaf x) (Leaf x) (Leaf x)
        ))
    =⟨ sym $ propFnIf {c = va == x && x == x && x == x } (λ g -> runIdentity (lensA (λ _ → CIdentity (Node b1 b2 b3 b4)) (g)) ) ⟩
        (if va == x && x == x && x == x 
        then runIdentity (lensA (λ _ → CIdentity (Node b1 b2 b3 b4)) (Leaf va))
        else runIdentity (lensA (λ _ → CIdentity (Node b1 b2 b3 b4)) (Node (Leaf va) (Leaf x) (Leaf x) (Leaf x))))
    =⟨⟩
        (if va == x && x == x && x == x 
        then Node (Node b1 b2 b3 b4) (Leaf va) (Leaf va) (Leaf va)
        else Node (Node b1 b2 b3 b4) (Leaf x) (Leaf x) (Leaf x))
    =⟨ ifTrueMap {c = va == x && x == x && x == x} 
        (λ p -> cong ((λ q -> Node (Node b1 b2 b3 b4) (Leaf q) (Leaf q) (Leaf q) )) 
        (eqToEquiv va x (andFst {va == x} p))) ⟩
        (if va == x && x == x && x == x 
        then Node (Node b1 b2 b3 b4) (Leaf x) (Leaf x) (Leaf x)
        else Node (Node b1 b2 b3 b4) (Leaf x) (Leaf x) (Leaf x))
    =⟨ propIfBranchesSame (Node (Node b1 b2 b3 b4) (Leaf x) (Leaf x) (Leaf x)) ⟩
        set lensA (Node b1 b2 b3 b4) (Leaf x)
    end
ValidLens-LensA-SetSet (Leaf va) (Leaf vb) (Node xa (Leaf x) (Leaf x₁) (Node xd xd₁ xd₂ xd₃)) = refl
ValidLens-LensA-SetSet (Leaf va) (Leaf vb) (Node xa (Leaf x) (Node xc xc₁ xc₂ xc₃) xd) = refl
ValidLens-LensA-SetSet (Leaf va) (Leaf vb) (Node xa (Node xb xb₁ xb₂ xb₃) xc xd) = refl
ValidLens-LensA-SetSet (Leaf va) (Leaf vb) (Node xa (Leaf xvb) (Leaf xvc) (Leaf xvd)) =
    begin
        set lensA (Leaf vb) (set lensA (Leaf va) (Node xa (Leaf xvb) (Leaf xvc) (Leaf xvd)))
    =⟨⟩
        runIdentity (lensA (λ _ → CIdentity (Leaf vb))
            (if va == xvb && xvb == xvc && xvc == xvd
            then Leaf va 
            else Node (Leaf va) (Leaf xvb) (Leaf xvc) (Leaf xvd)))
    =⟨ sym $ propFnIf {c = va == xvb && xvb == xvc && xvc == xvd } ((λ g -> runIdentity (lensA (λ _ → CIdentity (Leaf vb)) g))) ⟩
        (if va == xvb && xvb == xvc && xvc == xvd
        then (runIdentity (lensA (λ _ → CIdentity (Leaf vb)) (Leaf va)))
        else (runIdentity (lensA (λ _ → CIdentity (Leaf vb)) (Node (Leaf va) (Leaf xvb) (Leaf xvc) (Leaf xvd)))))
    =⟨⟩
        (if va == xvb && xvb == xvc && xvc == xvd
        then if vb == va && va == va && va == va then Leaf vb else Node (Leaf vb) (Leaf va) (Leaf va) (Leaf va) 
        else (if vb == xvb && xvb == xvc && xvc == xvd then Leaf vb else Node (Leaf vb) (Leaf xvb) (Leaf xvc) (Leaf xvd)) )
    =⟨ {!   !} ⟩
        (if va == xvb && xvb == xvc && xvc == xvd
        then Leaf vb 
        else (if vb == xvb && xvb == xvc && xvc == xvd then Leaf vb else Node (Leaf vb) (Leaf xvb) (Leaf xvc) (Leaf xvd)) )
    =⟨ ? ⟩
        (if vb == xvb && xvb == xvc && xvc == xvd then Leaf vb else Node (Leaf vb) (Leaf xvb) (Leaf xvc) (Leaf xvd))
    =⟨⟩
        set lensA (Leaf vb) (Node xa (Leaf xvb) (Leaf xvc) (Leaf xvd))
    end
ValidLens-LensA-SetSet (Leaf va) (Node b1 b2 b3 b4) (Node xa xb xc xd) =
    begin
        set lensA (Node b1 b2 b3 b4) (set lensA (Leaf va) (Node xa xb xc xd))
    =⟨ {!   !} ⟩
        {!   !}
    end
ValidLens-LensA-SetSet (Node a1 a2 a3 a4) (Leaf b) (Leaf x) = refl
ValidLens-LensA-SetSet (Node a1 a2 a3 a4) (Leaf b) (Node x1 x2 x3 x4) = refl
ValidLens-LensA-SetSet (Node a1 a2 a3 a4) (Node b1 b2 b3 b4) (Leaf x) = refl
ValidLens-LensA-SetSet (Node a1 a2 a3 a4) (Node b1 b2 b3 b4) (Node x1 x2 x3 x4) = refl

-- set lensA v2 (set lensA v1 vqt) ≡ set lensA v2 vqt

-- (v1 v2 : b) (s : a) -> 
-- postulate 
--     ValidLens-LensA-ViewSet : 
--         {t : Set} {{eqT : Eq t}} (dep : Nat) 
--         -> ViewSet (lensA {t} {dep})
--     ValidLens-LensA-SetView : 
--         {t : Set} {{eqT : Eq t}} (dep : Nat) 
--         -> SetView (lensA {t} {dep})
--     ValidLens-LensA-SetSet : 
--         {t : Set} {{eqT : Eq t}} (dep : Nat) 
--         -> SetSet (lensA {t} {dep})

-- ValidLens-LensA : {t : Set} {{eqT : Eq t}}
--     -> {dep : Nat}
--     -> ValidLens (ValidQuadrant t {S dep}) (ValidQuadrant t {dep})
-- ValidLens-LensA {dep = dep} = CValidLens lensA (ValidLens-LensA-ViewSet dep) (ValidLens-LensA-SetView dep) (ValidLens-LensA-SetSet dep)


-- --- Lens laws for lensB

-- postulate 
--     ValidLens-LensB-ViewSet : 
--         {t : Set} {{eqT : Eq t}} (dep : Nat) 
--         -> ViewSet (lensB {t} {dep})
--     ValidLens-LensB-SetView : 
--         {t : Set} {{eqT : Eq t}} (dep : Nat) 
--         -> SetView (lensB {t} {dep})
--     ValidLens-LensB-SetSet : 
--         {t : Set} {{eqT : Eq t}} (dep : Nat) 
--         -> SetSet (lensB {t} {dep})

-- ValidLens-LensB : {t : Set} {{eqT : Eq t}}
--     -> {dep : Nat}
--     -> ValidLens (ValidQuadrant t {S dep}) (ValidQuadrant t {dep})
-- ValidLens-LensB {dep = dep} = CValidLens lensB (ValidLens-LensB-ViewSet dep) (ValidLens-LensB-SetView dep) (ValidLens-LensB-SetSet dep)

-- --- Lens laws for lensC

-- postulate 
--     ValidLens-LensC-ViewSet : 
--         {t : Set} {{eqT : Eq t}} (dep : Nat) 
--         -> ViewSet (lensC {t} {dep})
--     ValidLens-LensC-SetView : 
--         {t : Set} {{eqT : Eq t}} (dep : Nat) 
--         -> SetView (lensC {t} {dep})
--     ValidLens-LensC-SetSet : 
--         {t : Set} {{eqT : Eq t}} (dep : Nat) 
--         -> SetSet (lensC {t} {dep})

-- ValidLens-LensC : {t : Set} {{eqT : Eq t}}
--     -> {dep : Nat}
--     -> ValidLens (ValidQuadrant t {S dep}) (ValidQuadrant t {dep})
-- ValidLens-LensC {dep = dep} = CValidLens lensC (ValidLens-LensC-ViewSet dep) (ValidLens-LensC-SetView dep) (ValidLens-LensC-SetSet dep)

-- --- Lens laws for lensD

-- postulate 
--     ValidLens-LensD-ViewSet : 
--         {t : Set} {{eqT : Eq t}} (dep : Nat) 
--         -> ViewSet (lensD {t} {dep})
--     ValidLens-LensD-SetView : 
--         {t : Set} {{eqT : Eq t}} (dep : Nat) 
--         -> SetView (lensD {t} {dep})
--     ValidLens-LensD-SetSet : 
--         {t : Set} {{eqT : Eq t}} (dep : Nat) 
--         -> SetSet (lensD {t} {dep})

-- ValidLens-LensD : {t : Set} {{eqT : Eq t}}
--     -> {dep : Nat}
--     -> ValidLens (ValidQuadrant t {S dep}) (ValidQuadrant t {dep})
-- ValidLens-LensD {dep = dep} = CValidLens lensD (ValidLens-LensD-ViewSet dep) (ValidLens-LensD-SetView dep) (ValidLens-LensD-SetSet dep)

-- ---- Lens laws for go

-- -- ValidLens-go : {t : Set} {{eqT : Eq t}}
-- --     -> (loc : Nat × Nat) -> (dep : Nat)
-- --     -> ValidLens (ValidQuadrant t {dep}) t

-- -- ValidLens-go-ViewSet :
-- --     {t : Set} {{eqT : Eq t}}
-- --     -> (loc : Nat × Nat) -> (dep : Nat)
-- --     -> ViewSet (go {t} loc dep)
-- -- ValidLens-go-ViewSet loc Z v cvq@(CValidQuadrant (Leaf x) {p}) = refl
-- -- ValidLens-go-ViewSet (x , y) dep@(S deps) v cvq@(CValidQuadrant qd {p}) =
-- --     begin
-- --         view (go (x , y) (S deps)) (set (go (x , y) (S deps)) v cvq) 
-- --     =⟨⟩
-- --         view (lensA ∘ (go (x , y) deps)) (set (lensA ∘ (go (x , y) deps)) v cvq) 
-- --     =⟨ prop-Composition-ViewSet (ValidLens-LensA) (ValidLens-go (x , y) deps) v cvq ⟩
-- --         v
-- --     end
--     -- ifc y < pow 2 deps
--     -- then (λ {{p1}} ->
--     --     ifc x < pow 2 deps
--     --     then (λ {{q1}} ->
--     --         begin
--     --             view (go (x , y) (S deps)) (set (go (x , y) (S deps)) v cvq)
--     --         =⟨ cong (λ h -> view (h {f}) (set (h {f}) v cvq)) refl ⟩
--     --             view (go (x , y) (S deps)) (set (go (x , y) (S deps)) v cvq)
--     --         =⟨ {!   !} ⟩
--     --             v
--     --         end
--     --     )
--     --     else (λ {{q2}} ->
--     --         {!   !}
--     --     )
--     -- )
--     -- else (λ {{p2}} ->
--     --     ifc x < pow 2 deps
--     --     then (λ {{q1}} ->
--     --         {!   !}
--     --     )
--     --     else (λ {{q2}} ->
--     --         {!   !}
--     --     )
--     -- ) where
--     --     ta : (CLens (ValidQuadrant t {dep}) t) -> t
--     --     ta = {!   !}
--     -- begin
--     --     view (go (x , y) (S deps)) (set (go (x , y) (S deps)) v (CValidQuadrant qd))
--     -- =⟨⟩
--     --     {! !}
--     -- =⟨ {!   !} ⟩
--     --     v
--     -- end

-- -- postulate 
-- --     ValidLens-go-SetView : 
-- --         {t : Set} {{eqT : Eq t}}
-- --         -> (loc : Nat × Nat) -> (dep : Nat)
-- --         -> SetView (go {t} loc dep)
-- --     ValidLens-go-SetSet : 
-- --         {t : Set} {{eqT : Eq t}}
-- --         -> (loc : Nat × Nat) -> (dep : Nat)
-- --         -> SetSet (go {t} loc dep)

-- -- ValidLens-go {t} {{eqT}} loc dep = CValidLens (go loc dep) (ValidLens-go-ViewSet loc dep) (ValidLens-go-SetView loc dep) (ValidLens-go-SetSet loc dep)
