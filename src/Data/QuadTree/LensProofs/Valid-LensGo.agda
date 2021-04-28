module Data.QuadTree.LensProofs.Valid-LensGo where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.QuadTree.Lens
open import Data.QuadTree.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive
open import Data.QuadTree.LensProofs.Lens
open import Data.QuadTree.LensProofs.LensPostulates
open import Data.QuadTree.LensProofs.LensComposition

---- Lens laws for go

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
