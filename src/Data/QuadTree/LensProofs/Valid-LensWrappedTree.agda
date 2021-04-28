module Data.QuadTree.LensProofs.Valid-LensWrappedTree where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.QuadTree.Lens
open import Data.QuadTree.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive
open import Data.QuadTree.LensProofs.Lens
open import Data.QuadTree.LensProofs.LensPostulates
open import Data.QuadTree.LensProofs.LensComposition

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