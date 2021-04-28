module Data.QuadTree.LensProofs.LensPostulates where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.QuadTree.Lens
open import Data.QuadTree.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive
open import Data.QuadTree.LensProofs.Lens

---- Lens postulates
-- These are provable using the isomorphism to the getter+setter style
-- However, defining this isomorphism is quite a bit of work, so I didn't do it for now

postulate 
    -- view (l1 ∘ l2) ≡ view l2 ∘ view l1
    -- This is clearly true from how view works
    prop-view-compose : {a b c : Set} 
        -> (l1 : ValidLens a b)
        -> (l2 : ValidLens b c)
        -> (v : a)
        -> (view ((toLens l1) ∘ (toLens l2))) v ≡ (view (toLens l2) ∘ view (toLens l1)) v
    -- set (l1 ∘ l2) ≡ over l1 (set l2 t) v
    -- This is clearly true from how set works
    prop-set-compose : {a b c : Set} 
        -> (l1 : ValidLens a b)
        -> (l2 : ValidLens b c)
        -> (v : a) (t : c)
        -> (set ((toLens l1) ∘ (toLens l2))) t v ≡ over (toLens l1) (set (toLens l2) t) v
    -- over l ≡ set l (view l v) v
    -- This is clearly true from how over works
    prop-over-is-setget : {a b : Set} 
        -> (l : ValidLens a b)
        -> (f : b -> b) (v : a)
        -> over (toLens l) f v ≡ set (toLens l) (f (view (toLens l) v)) v

-- We can merge postulate 2 and 3

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