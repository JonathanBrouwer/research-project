module Data.QuadTree.LensLaws where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.QuadTree.Lens
open import Data.QuadTree.Logic
open import Data.QuadTree.PropDepthRelation
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
    {t : Set} {{eqT : Eq t}} (dep : Nat) 
    -> ViewSet (lensWrappedTree {t} {dep})
ValidLens-WrappedTree-ViewSet {t} dep (CValidQuadrant qdn {pn}) (CValidQuadTree (Wrapper qdo (w , h)) {p} {q}) = refl

ValidLens-WrappedTree-SetView : 
    {t : Set} {{eqT : Eq t}} (dep : Nat) 
    -> SetView (lensWrappedTree {t} {dep})
ValidLens-WrappedTree-SetView {t} dep (CValidQuadTree (Wrapper qdo (w , h)) {p} {q}) = refl

ValidLens-WrappedTree-SetSet : 
    {t : Set} {{eqT : Eq t}} (dep : Nat) 
    -> SetSet (lensWrappedTree {t} {dep})
ValidLens-WrappedTree-SetSet {t} dep (CValidQuadrant qd1 {p1}) (CValidQuadrant qd2 {p2}) (CValidQuadTree (Wrapper qdo (w , h)) {p} {q}) = refl

ValidLens-WrappedTree :
    {t : Set} {{eqT : Eq t}} (dep : Nat) 
    -> ValidLens (ValidQuadTree t {dep}) (ValidQuadrant t {dep})
ValidLens-WrappedTree dep = CValidLens lensWrappedTree (ValidLens-WrappedTree-ViewSet dep) (ValidLens-WrappedTree-SetView dep) (ValidLens-WrappedTree-SetSet dep)

--- Lens laws for lensLeaf

ValidLens-Leaf-ViewSet : 
    {t : Set} {{eqT : Eq t}}
    -> ViewSet (lensLeaf {t})
ValidLens-Leaf-ViewSet {t} v (CValidQuadrant (Leaf lv) {pn}) = refl

ValidLens-Leaf-SetView : 
    {t : Set} {{eqT : Eq t}}
    -> SetView (lensLeaf {t})
ValidLens-Leaf-SetView {t} (CValidQuadrant (Leaf lv) {IsTrue.itsTrue}) = refl

ValidLens-Leaf-SetSet : 
    {t : Set} {{eqT : Eq t}}
    -> SetSet (lensLeaf {t})
ValidLens-Leaf-SetSet {t} v1 v2 (CValidQuadrant (Leaf lv) {pn}) = refl

ValidLens-Leaf :
    {t : Set} {{eqT : Eq t}}
    -> ValidLens (ValidQuadrant t {0}) t
ValidLens-Leaf = CValidLens lensLeaf ValidLens-Leaf-ViewSet ValidLens-Leaf-SetView ValidLens-Leaf-SetSet


--- Lens laws for lensA

-- TODO: Add {p} to constructors
-- ValidLens-LensA-ViewSet : 
--     {t : Set} {{eqT : Eq t}} (dep : Nat) 
--     -> ViewSet (lensA {t} {dep})
-- ValidLens-LensA-ViewSet {t} {{eqT}} dep vqi@(CValidQuadrant (Leaf vi) {pi}) vqo@(CValidQuadrant (Leaf vo) {po}) =
--     begin
--         view lensA (set lensA vqi vqo)
--     =⟨⟩
--         ta
--             (ifc not (vi == vo && vo == vo && vo == vo)
--                 then (λ {{pp}} -> CValidQuadrant (Node (Leaf vi) (Leaf vo) (Leaf vo) (Leaf vo)) {andCombine (zeroLteAny dep) pp})
--                 else (CValidQuadrant (Leaf vi) {IsTrue.itsTrue}))
--     =⟨ sym (propFnIfc (not (vi == vo && vo == vo && vo == vo)) ta) ⟩
--         (ifc not (vi == vo && vo == vo && vo == vo)
--             then (λ {{pp}} -> ta (CValidQuadrant (Node (Leaf vi) (Leaf vo) (Leaf vo) (Leaf vo)) {andCombine (zeroLteAny dep) pp} ))
--             else (ta (CValidQuadrant (Leaf vi) {IsTrue.itsTrue})))
--     =⟨⟩
--         (ifc not (vi == vo && vo == vo && vo == vo)
--             then (CValidQuadrant (Leaf vi) {andCombine (zeroLteAny dep) IsTrue.itsTrue})
--             else (CValidQuadrant (Leaf vi) {andCombine (zeroLteAny dep) IsTrue.itsTrue}))
--     =⟨ propIfcBranchesSame {c = not (vi == vo && vo == vo && vo == vo)} (CValidQuadrant (Leaf vi)) ⟩
--         (CValidQuadrant (Leaf vi))
--     =⟨ {!   !} ⟩
--         (CValidQuadrant (Leaf vi))
--     end where
--         ta : ValidQuadrant t {S dep} -> ValidQuadrant t {dep}
--         ta y = getConst (lensA CConst (y))
-- ValidLens-LensA-ViewSet {t} dep vqi@(CValidQuadrant (Node ai bi ci di)) vqo@(CValidQuadrant (Leaf vo)) = {!   !}
-- ValidLens-LensA-ViewSet {t} dep (CValidQuadrant (Leaf vi)) (CValidQuadrant (Node oa ob oc od)) = {!   !}
-- ValidLens-LensA-ViewSet {t} dep (CValidQuadrant (Node ai bi ci di)) (CValidQuadrant (Node oa ob oc od)) = {!   !}

postulate 
    ValidLens-LensA-ViewSet : 
        {t : Set} {{eqT : Eq t}} (dep : Nat) 
        -> ViewSet (lensA {t} {dep})
    ValidLens-LensA-SetView : 
        {t : Set} {{eqT : Eq t}} (dep : Nat) 
        -> SetView (lensA {t} {dep})
    ValidLens-LensA-SetSet : 
        {t : Set} {{eqT : Eq t}} (dep : Nat) 
        -> SetSet (lensA {t} {dep})

ValidLens-LensA : {t : Set} {{eqT : Eq t}}
    -> {dep : Nat}
    -> ValidLens (ValidQuadrant t {S dep}) (ValidQuadrant t {dep})
ValidLens-LensA {dep = dep} = CValidLens lensA (ValidLens-LensA-ViewSet dep) (ValidLens-LensA-SetView dep) (ValidLens-LensA-SetSet dep)


--- Lens laws for lensB

postulate 
    ValidLens-LensB-ViewSet : 
        {t : Set} {{eqT : Eq t}} (dep : Nat) 
        -> ViewSet (lensB {t} {dep})
    ValidLens-LensB-SetView : 
        {t : Set} {{eqT : Eq t}} (dep : Nat) 
        -> SetView (lensB {t} {dep})
    ValidLens-LensB-SetSet : 
        {t : Set} {{eqT : Eq t}} (dep : Nat) 
        -> SetSet (lensB {t} {dep})

ValidLens-LensB : {t : Set} {{eqT : Eq t}}
    -> {dep : Nat}
    -> ValidLens (ValidQuadrant t {S dep}) (ValidQuadrant t {dep})
ValidLens-LensB {dep = dep} = CValidLens lensB (ValidLens-LensB-ViewSet dep) (ValidLens-LensB-SetView dep) (ValidLens-LensB-SetSet dep)

--- Lens laws for lensC

postulate 
    ValidLens-LensC-ViewSet : 
        {t : Set} {{eqT : Eq t}} (dep : Nat) 
        -> ViewSet (lensC {t} {dep})
    ValidLens-LensC-SetView : 
        {t : Set} {{eqT : Eq t}} (dep : Nat) 
        -> SetView (lensC {t} {dep})
    ValidLens-LensC-SetSet : 
        {t : Set} {{eqT : Eq t}} (dep : Nat) 
        -> SetSet (lensC {t} {dep})

ValidLens-LensC : {t : Set} {{eqT : Eq t}}
    -> {dep : Nat}
    -> ValidLens (ValidQuadrant t {S dep}) (ValidQuadrant t {dep})
ValidLens-LensC {dep = dep} = CValidLens lensC (ValidLens-LensC-ViewSet dep) (ValidLens-LensC-SetView dep) (ValidLens-LensC-SetSet dep)

--- Lens laws for lensD

postulate 
    ValidLens-LensD-ViewSet : 
        {t : Set} {{eqT : Eq t}} (dep : Nat) 
        -> ViewSet (lensD {t} {dep})
    ValidLens-LensD-SetView : 
        {t : Set} {{eqT : Eq t}} (dep : Nat) 
        -> SetView (lensD {t} {dep})
    ValidLens-LensD-SetSet : 
        {t : Set} {{eqT : Eq t}} (dep : Nat) 
        -> SetSet (lensD {t} {dep})

ValidLens-LensD : {t : Set} {{eqT : Eq t}}
    -> {dep : Nat}
    -> ValidLens (ValidQuadrant t {S dep}) (ValidQuadrant t {dep})
ValidLens-LensD {dep = dep} = CValidLens lensD (ValidLens-LensD-ViewSet dep) (ValidLens-LensD-SetView dep) (ValidLens-LensD-SetSet dep)

---- Lens laws for go

-- ValidLens-go : {t : Set} {{eqT : Eq t}}
--     -> (loc : Nat × Nat) -> (dep : Nat)
--     -> ValidLens (ValidQuadrant t {dep}) t

-- ValidLens-go-ViewSet :
--     {t : Set} {{eqT : Eq t}}
--     -> (loc : Nat × Nat) -> (dep : Nat)
--     -> ViewSet (go {t} loc dep)
-- ValidLens-go-ViewSet loc Z v cvq@(CValidQuadrant (Leaf x) {p}) = refl
-- ValidLens-go-ViewSet (x , y) dep@(S deps) v cvq@(CValidQuadrant qd {p}) =
--     begin
--         view (go (x , y) (S deps)) (set (go (x , y) (S deps)) v cvq) 
--     =⟨⟩
--         view (lensA ∘ (go (x , y) deps)) (set (lensA ∘ (go (x , y) deps)) v cvq) 
--     =⟨ prop-Composition-ViewSet (ValidLens-LensA) (ValidLens-go (x , y) deps) v cvq ⟩
--         v
--     end
    -- ifc y < pow 2 deps
    -- then (λ {{p1}} ->
    --     ifc x < pow 2 deps
    --     then (λ {{q1}} ->
    --         begin
    --             view (go (x , y) (S deps)) (set (go (x , y) (S deps)) v cvq)
    --         =⟨ cong (λ h -> view (h {f}) (set (h {f}) v cvq)) refl ⟩
    --             view (go (x , y) (S deps)) (set (go (x , y) (S deps)) v cvq)
    --         =⟨ {!   !} ⟩
    --             v
    --         end
    --     )
    --     else (λ {{q2}} ->
    --         {!   !}
    --     )
    -- )
    -- else (λ {{p2}} ->
    --     ifc x < pow 2 deps
    --     then (λ {{q1}} ->
    --         {!   !}
    --     )
    --     else (λ {{q2}} ->
    --         {!   !}
    --     )
    -- ) where
    --     ta : (CLens (ValidQuadrant t {dep}) t) -> t
    --     ta = {!   !}
    -- begin
    --     view (go (x , y) (S deps)) (set (go (x , y) (S deps)) v (CValidQuadrant qd))
    -- =⟨⟩
    --     {! !}
    -- =⟨ {!   !} ⟩
    --     v
    -- end

-- postulate 
--     ValidLens-go-SetView : 
--         {t : Set} {{eqT : Eq t}}
--         -> (loc : Nat × Nat) -> (dep : Nat)
--         -> SetView (go {t} loc dep)
--     ValidLens-go-SetSet : 
--         {t : Set} {{eqT : Eq t}}
--         -> (loc : Nat × Nat) -> (dep : Nat)
--         -> SetSet (go {t} loc dep)

-- ValidLens-go {t} {{eqT}} loc dep = CValidLens (go loc dep) (ValidLens-go-ViewSet loc dep) (ValidLens-go-SetView loc dep) (ValidLens-go-SetSet loc dep)
