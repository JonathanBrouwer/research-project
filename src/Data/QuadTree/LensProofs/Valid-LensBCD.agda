module Data.QuadTree.LensProofs.Valid-LensBCD where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Lens.Lens
open import Data.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive
open import Data.Lens.Proofs.LensLaws
open import Data.Lens.Proofs.LensPostulates
open import Data.Lens.Proofs.LensComposition

--- Lens laws for lensB

postulate 
    ValidLens-LensB-ViewSet : 
        {t : Set} {{eqT : Eq t}}
        -> ViewSet (lensB {t})
    ValidLens-LensB-SetView : 
        {t : Set} {{eqT : Eq t}} 
        -> SetView (lensB {t})
    ValidLens-LensB-SetSet : 
        {t : Set} {{eqT : Eq t}}
        -> SetSet (lensB {t})

ValidLens-LensB : {t : Set} {{eqT : Eq t}}
    -> ValidLens (Quadrant t) (Quadrant t)
ValidLens-LensB = CValidLens lensB (ValidLens-LensB-ViewSet) (ValidLens-LensB-SetView) (ValidLens-LensB-SetSet)

--- Lens laws for lensC

postulate 
    ValidLens-LensC-ViewSet : 
        {t : Set} {{eqT : Eq t}}
        -> ViewSet (lensC {t})
    ValidLens-LensC-SetView : 
        {t : Set} {{eqT : Eq t}} 
        -> SetView (lensC {t})
    ValidLens-LensC-SetSet : 
        {t : Set} {{eqT : Eq t}} 
        -> SetSet (lensC {t})

ValidLens-LensC : {t : Set} {{eqT : Eq t}}
    -> ValidLens (Quadrant t) (Quadrant t)
ValidLens-LensC = CValidLens lensC (ValidLens-LensC-ViewSet) (ValidLens-LensC-SetView) (ValidLens-LensC-SetSet)

--- Lens laws for lensD

postulate 
    ValidLens-LensD-ViewSet : 
        {t : Set} {{eqT : Eq t}} 
        -> ViewSet (lensD {t})
    ValidLens-LensD-SetView : 
        {t : Set} {{eqT : Eq t}} 
        -> SetView (lensD {t})
    ValidLens-LensD-SetSet : 
        {t : Set} {{eqT : Eq t}} 
        -> SetSet (lensD {t})

ValidLens-LensD : {t : Set} {{eqT : Eq t}}
    -> ValidLens (Quadrant t) (Quadrant t)
ValidLens-LensD = CValidLens lensD (ValidLens-LensD-ViewSet) (ValidLens-LensD-SetView) (ValidLens-LensD-SetSet)