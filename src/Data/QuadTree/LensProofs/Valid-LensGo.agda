module Data.QuadTree.LensProofs.Valid-LensGo where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Lens.Lens
open import Data.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive
open import Data.Lens.Proofs.LensLaws
open import Data.Lens.Proofs.LensPostulates
open import Data.Lens.Proofs.LensComposition
open import Data.QuadTree.LensProofs.Valid-LensLeaf
open import Data.QuadTree.LensProofs.Valid-LensA
open import Data.QuadTree.LensProofs.Valid-LensBCD

---- Lens laws for go

ValidLens-go-ViewSet :
    {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (dep : Nat)
    -> ViewSet (go {t} loc dep)

postulate 
    ValidLens-go-SetView : 
        {t : Set} {{eqT : Eq t}}
        -> (loc : Nat × Nat) -> (dep : Nat)
        -> SetView (go {t} loc dep)
    ValidLens-go-SetSet : 
        {t : Set} {{eqT : Eq t}}
        -> (loc : Nat × Nat) -> (dep : Nat)
        -> SetSet (go {t} loc dep)
    
ValidLens-go-ViewSet loc Z v cvq@(CVQuadrant (Leaf x)) = refl
ValidLens-go-ViewSet {t} loc@(x , y) dep@(S deps) v cvq@(CVQuadrant qd) = 
    begin
        view ( go (x , y) (S deps) ) (set ( go (x , y) (S deps) ) v cvq)
    -- =⟨⟩
    --     getConst (
    --         ifc y < pow 2 deps then
    --             ifc x < pow 2 deps 
    --                 then lensA (go (x , y) deps CConst) (runIdentity (
    --                     ifc y < pow 2 deps then
    --                         ifc x < pow 2 deps 
    --                             then lensA (go (x , y) deps (λ _ → CIdentity v) ) cvq
    --                             else (λ {{px}} -> lensB (go ((_-_ x (pow 2 deps) {{px}}) , y) deps (λ _ → CIdentity v) ) cvq)
    --                     else (λ {{py}} ->
    --                         ifc x < pow 2 deps 
    --                             then lensC (go (x , (_-_ y (pow 2 deps) {{py}})) deps (λ _ → CIdentity v) ) cvq
    --                             else (λ {{px}} -> lensD (go ((_-_ x (pow 2 deps) {{px}}) , (_-_ y (pow 2 deps) {{py}})) deps (λ _ → CIdentity v) ) cvq)
    --                     )))
    --                 else lensB (go ((x - pow 2 deps) , y) deps CConst) (runIdentity (
    --                     ifc y < pow 2 deps then
    --                         ifc x < pow 2 deps 
    --                             then lensA (go (x , y) deps (λ _ → CIdentity v) ) cvq
    --                             else (λ {{px}} -> lensB (go ((_-_ x (pow 2 deps) {{px}}) , y) deps (λ _ → CIdentity v) ) cvq)
    --                     else (λ {{py}} ->
    --                         ifc x < pow 2 deps 
    --                             then lensC (go (x , (_-_ y (pow 2 deps) {{py}})) deps (λ _ → CIdentity v) ) cvq
    --                             else (λ {{px}} -> lensD (go ((_-_ x (pow 2 deps) {{px}}) , (_-_ y (pow 2 deps) {{py}})) deps (λ _ → CIdentity v) ) cvq)
    --                     )))
    --         else 
    --             ifc x < pow 2 deps 
    --                 then lensC (go (x , (y - pow 2 deps)) deps CConst) (runIdentity (
    --                     ifc y < pow 2 deps then
    --                         ifc x < pow 2 deps 
    --                             then lensA (go (x , y) deps (λ _ → CIdentity v) ) cvq
    --                             else (λ {{px}} -> lensB (go ((_-_ x (pow 2 deps) {{px}}) , y) deps (λ _ → CIdentity v) ) cvq)
    --                     else (λ {{py}} ->
    --                         ifc x < pow 2 deps 
    --                             then lensC (go (x , (_-_ y (pow 2 deps) {{py}})) deps (λ _ → CIdentity v) ) cvq
    --                             else (λ {{px}} -> lensD (go ((_-_ x (pow 2 deps) {{px}}) , (_-_ y (pow 2 deps) {{py}})) deps (λ _ → CIdentity v) ) cvq)
    --                     )))
    --                 else lensD (go ((x - pow 2 deps) , (y - pow 2 deps)) deps CConst) (runIdentity (
    --                     ifc y < pow 2 deps then
    --                         ifc x < pow 2 deps 
    --                             then lensA (go (x , y) deps (λ _ → CIdentity v) ) cvq
    --                             else (λ {{px}} -> lensB (go ((_-_ x (pow 2 deps) {{px}}) , y) deps (λ _ → CIdentity v) ) cvq)
    --                     else (λ {{py}} ->
    --                         ifc x < pow 2 deps 
    --                             then lensC (go (x , (_-_ y (pow 2 deps) {{py}})) deps (λ _ → CIdentity v) ) cvq
    --                             else (λ {{px}} -> lensD (go ((_-_ x (pow 2 deps) {{px}}) , (_-_ y (pow 2 deps) {{py}})) deps (λ _ → CIdentity v) ) cvq)
    --                     ))))
    =⟨ propFnDistributeIfc2 (y < pow 2 deps) (x < pow 2 deps) (λ g -> getConst g) ⟩
        (ifc y < pow 2 deps then
            ifc x < pow 2 deps 
                then (getConst (lensA (go (x , y) deps CConst) (runIdentity (
                    ifc y < pow 2 deps then
                        ifc x < pow 2 deps 
                            then lensA (go (x , y) deps (λ _ → CIdentity v) ) cvq
                            else (λ {{px}} -> lensB (go ((_-_ x (pow 2 deps) {{px}}) , y) deps (λ _ → CIdentity v) ) cvq)
                    else (λ {{py}} ->
                        ifc x < pow 2 deps 
                            then lensC (go (x , (_-_ y (pow 2 deps) {{py}})) deps (λ _ → CIdentity v) ) cvq
                            else (λ {{px}} -> lensD (go ((_-_ x (pow 2 deps) {{px}}) , (_-_ y (pow 2 deps) {{py}})) deps (λ _ → CIdentity v) ) cvq)
                    )))))
                else (getConst (lensB (go ((x - pow 2 deps) , y) deps CConst) (runIdentity (
                    ifc y < pow 2 deps then
                        ifc x < pow 2 deps 
                            then lensA (go (x , y) deps (λ _ → CIdentity v) ) cvq
                            else (λ {{px}} -> lensB (go ((_-_ x (pow 2 deps) {{px}}) , y) deps (λ _ → CIdentity v) ) cvq)
                    else (λ {{py}} ->
                        ifc x < pow 2 deps 
                            then lensC (go (x , (_-_ y (pow 2 deps) {{py}})) deps (λ _ → CIdentity v) ) cvq
                            else (λ {{px}} -> lensD (go ((_-_ x (pow 2 deps) {{px}}) , (_-_ y (pow 2 deps) {{py}})) deps (λ _ → CIdentity v) ) cvq)
                    )))))
        else 
            ifc x < pow 2 deps 
                then (getConst (lensC (go (x , (y - pow 2 deps)) deps CConst) (runIdentity (
                    ifc y < pow 2 deps then
                        ifc x < pow 2 deps 
                            then lensA (go (x , y) deps (λ _ → CIdentity v) ) cvq
                            else (λ {{px}} -> lensB (go ((_-_ x (pow 2 deps) {{px}}) , y) deps (λ _ → CIdentity v) ) cvq)
                    else (λ {{py}} ->
                        ifc x < pow 2 deps 
                            then lensC (go (x , (_-_ y (pow 2 deps) {{py}})) deps (λ _ → CIdentity v) ) cvq
                            else (λ {{px}} -> lensD (go ((_-_ x (pow 2 deps) {{px}}) , (_-_ y (pow 2 deps) {{py}})) deps (λ _ → CIdentity v) ) cvq)
                    )))))
                else (getConst (lensD (go ((x - pow 2 deps) , (y - pow 2 deps)) deps CConst) (runIdentity (
                    ifc y < pow 2 deps then
                        ifc x < pow 2 deps 
                            then lensA (go (x , y) deps (λ _ → CIdentity v) ) cvq
                            else (λ {{px}} -> lensB (go ((_-_ x (pow 2 deps) {{px}}) , y) deps (λ _ → CIdentity v) ) cvq)
                    else (λ {{py}} ->
                        ifc x < pow 2 deps 
                            then lensC (go (x , (_-_ y (pow 2 deps) {{py}})) deps (λ _ → CIdentity v) ) cvq
                            else (λ {{px}} -> lensD (go ((_-_ x (pow 2 deps) {{px}}) , (_-_ y (pow 2 deps) {{py}})) deps (λ _ → CIdentity v) ) cvq)
                    ))))))
    =⟨ {!   !} ⟩
        v
    end


ValidLens-go : {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (dep : Nat)
    -> ValidLens (VQuadrant t {dep}) t
ValidLens-go {t} {{eqT}} (x , y) dep = CValidLens (go (x , y) dep) (ValidLens-go-ViewSet (x , y) dep) (ValidLens-go-SetView (x , y) dep) (ValidLens-go-SetSet (x , y) dep)

                        -- (λ f v₁ →
                        --     ifc y < pow 2 deps then
                        --         ifc x < pow 2 deps 
                        --             then lensA (go (x , y) deps f) v₁ 
                        --             else lensB (go ((x - pow 2 deps) , y) deps f) v₁
                        --     else 
                        --         ifc x < pow 2 deps 
                        --             then lensC (go (x , (y - pow 2 deps)) deps f) v₁
                        --             else lensD (go ((x - pow 2 deps) , (y - pow 2 deps)) deps f) v₁)