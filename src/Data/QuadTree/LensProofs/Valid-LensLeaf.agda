module Data.QuadTree.LensProofs.Valid-LensLeaf where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.QuadTree.Lens
open import Data.QuadTree.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive
open import Data.QuadTree.LensProofs.Lens
open import Data.QuadTree.LensProofs.LensPostulates
open import Data.QuadTree.LensProofs.LensComposition

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