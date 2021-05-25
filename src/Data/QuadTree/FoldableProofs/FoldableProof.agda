-- {-# OPTIONS --show-implicit --show-irrelevant #-}
module Data.QuadTree.FoldableProofs.FoldableProof where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Logic
open import Data.QuadTree.Implementation.Definition
open import Data.QuadTree.Implementation.ValidTypes
open import Data.QuadTree.Implementation.QuadrantLenses
open import Data.QuadTree.Implementation.SafeFunctions
open import Data.QuadTree.Implementation.PropDepthRelation
open import Data.QuadTree.Implementation.Foldable

-- All proofs for Foldables

-- foldr f z t = appEndo (foldMap (Endo . f) t ) z
-- foldl f z t = appEndo (getDual (foldMap (Dual . Endo . flip f) t)) z
-- fold = foldMap id
-- length = getSum . foldMap (Sum . const 1)
-- I didn't change the default implementations of foldl/foldr/fold/length, so these laws should all hold

-- However, I will proof that the length of the quadtree is equal to width * height.
-- lengthₑ quadtreeFoldable vqt ≡ size vqt

size : {t : Set} {{eqT : Eq t}} {dep : Nat} -> (vqt : VQuadTree t {dep}) -> Nat
size (CVQuadTree (Wrapper (w , h) x₁)) = w * h

lengthₙ : {t : Set → Set} ⦃ r : Foldable t ⦄ {a : Set} → t a → Nat
lengthₙ {{r}} = foldMap {{r}} {{ MonoidSum }} (const 1)

length-replicate : {t : Set} (n : Nat) (v : t) -> lengthₙ (replicate n v) ≡ n
length-replicate {t} Z v = refl
length-replicate {t} (S n) v =
    begin
        lengthₙ (replicate (S n) v)
    =⟨⟩
        S (lengthₙ (replicate n v))
    =⟨ cong S (length-replicate n v ) ⟩
        S n
    end

length-concat-sub : {t : Set} -> (list : List t) (lists : List (List t)) -> lengthₙ (list ++ concat lists) ≡ lengthₙ list + lengthₙ (concat lists)
length-concat-sub {t} [] lists = refl
length-concat-sub {t} (x ∷ xs) lists = 
    begin
        lengthₙ ((x ∷ xs) ++ concat lists)
    =⟨⟩
        S (lengthₙ (xs ++ concat lists)) 
    =⟨ cong S (length-concat-sub xs lists) ⟩
        lengthₙ (x ∷ xs) + lengthₙ (concat lists)
    end

length-concat : {t : Set} -> (lists : List (List t)) -> lengthₙ (concat lists) ≡ sum (map lengthₙ lists)
length-concat {t} [] = refl
length-concat {t} (list ∷ lists) =
    begin
        lengthₙ (concat (list ∷ lists))
    =⟨⟩
        lengthₙ (list ++ concat lists)
    =⟨ length-concat-sub list lists ⟩
        lengthₙ list + lengthₙ (concat lists)
    =⟨ cong (λ q -> lengthₙ list + q) (length-concat lists) ⟩
        lengthₙ list + sum (map lengthₙ lists)
    =⟨⟩
        sum (map lengthₙ (list ∷ lists))
    end

concat-nothing : {t : Set} -> (list : List t) -> list ++ [] ≡ list
concat-nothing [] = refl
concat-nothing (x ∷ list) = cong (λ z → x ∷ z) (concat-nothing list)

diff-n-zero : (n : Nat) -> diff n Z ≡ n
diff-n-zero Z = refl
diff-n-zero (S n) = refl

length-tilesQd : {t : Set} {{eqT : Eq t}} {dep : Nat} -> (vqd : VQuadrant t {dep})
    -> (x1 y1 x2 y2 : Nat)
    -> sum (map lengthₙ (map expand (tilesQd {dep = dep} vqd (RegionC (x1 , y1) (x2 , y2))))) ≡ diff x2 x1 * diff y2 y1
length-tilesQd {t} {dep = dep} (CVQuadrant (Leaf v) {p}) x1 y1 x2 y2 =
    begin
        sum (map lengthₙ (map expand (tilesQd {dep = dep} (CVQuadrant (Leaf v) {p}) (RegionC (x1 , y1) (x2 , y2)))))
    =⟨⟩
        lengthₙ (replicate (diff x2 x1 * diff y2 y1) v) + 0
    =⟨ add-comm _ 0 ⟩
        lengthₙ (replicate (diff x2 x1 * diff y2 y1) v)
    =⟨ length-replicate (diff x2 x1 * diff y2 y1) v ⟩
        diff x2 x1 * diff y2 y1
    end
length-tilesQd {dep = S dep} (CVQuadrant (Node a b c d) {p}) x1 y1 x2 y2 =
    begin
        sum (map lengthₙ (map expand (tilesQd {dep = S dep} (CVQuadrant (Node a b c d) {p}) (RegionC (x1 , y1) (x2 , y2)))))
    =⟨⟩
        sum (map lengthₙ (map expand (
            tilesQd (CVQuadrant a) (RegionC (x1 , y1) (mid + x1 , mid + y1)) 
            ++ tilesQd (CVQuadrant b) (RegionC ((mid + x1) , y1) ((mid + (mid + x1)) , (mid + y1))) 
            ++ tilesQd (CVQuadrant c) (RegionC (x1 , (mid + y1)) ((mid + x1) , (mid + (mid + y1)))) 
            ++ tilesQd (CVQuadrant d) (RegionC ((mid + x1) , (mid + y1)) ((mid + (mid + x1)) , (mid + (mid + y1))))
        )))
    =⟨ {!   !} ⟩
        diff x2 x1 * diff y2 y1
    end where
        mid = pow 2 dep

    -- begin
    --     sum (map lengthₙ (map expand (tilesQd {dep = dep} vqd (RegionC (x1 , y1) (x2 , y2)))))
    -- -- =⟨ ? ⟩
        -- sum (map lengthₙ (map expand (
        --     tilesQd (CVQuadrant a) (RegionC (0 , 0) (mid + 0 , mid + 0)) ++
        --     tilesQd (CVQuadrant b) (RegionC ((pow 2 deps + 0) , 0) ((pow 2 deps + (pow 2 deps + 0)) , (pow 2 deps + 0))) ++ 
        --     tilesQd (CVQuadrant c) (RegionC (0 , (pow 2 deps + 0)) ((pow 2 deps + 0) , (pow 2 deps + (pow 2 deps + 0)))) ++
        --     tilesQd (CVQuadrant d) (RegionC ((pow 2 deps + 0) , (pow 2 deps + 0)) ((pow 2 deps + (pow 2 deps + 0)) , (pow 2 deps + (pow 2 deps + 0))))
        -- )))
    -- =⟨ {!   !} ⟩
    --     diff x2 x1 * diff y2 y1
    -- end

proof-length : {t : Set} {{eqT : Eq t}} {dep : Nat} -> (vqt : VQuadTree t {dep}) -> lengthₑ quadtreeFoldable vqt ≡ size vqt
proof-length {t} ⦃ eqT ⦄ {dep} vqt@(CVQuadTree (Wrapper (w , h) qd) {p1} {p2}) =
    begin
        lengthₑ quadtreeFoldable vqt
    =⟨⟩
        lengthₙ (concat (map expand (tilesQd {dep = dep} (CVQuadrant qd {p1}) (RegionC (0 , 0) (w , h)))))
    =⟨ length-concat (map expand (tilesQd {dep = dep} (CVQuadrant qd {p1}) (RegionC (0 , 0) (w , h)))) ⟩
        sum (map lengthₙ (map expand (tilesQd {dep = dep} (CVQuadrant qd {p1}) (RegionC (0 , 0) (w , h)))))
    =⟨ length-tilesQd {dep = dep} (CVQuadrant qd {p1}) 0 0 w h ⟩
        w * h
    end