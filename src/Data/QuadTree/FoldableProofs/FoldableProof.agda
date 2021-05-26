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

length-replicateₙ : {t : Set} (n : Nat) (v : t) -> lengthₙ (replicateₙ n v) ≡ n
length-replicateₙ {t} Z v = refl
length-replicateₙ {t} (S n) v =
    begin
        lengthₙ (replicateₙ (S n) v)
    =⟨⟩
        S (lengthₙ (replicateₙ n v))
    =⟨ cong S (length-replicateₙ n v ) ⟩
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

map-concat : {s t : Set} -> (a b : List s)
    -> (f : s -> t)
    -> map f (a ++ b) ≡ map f a ++ map f b
map-concat [] b f = refl
map-concat (a ∷ as) b f = cong (λ z → f a ∷ z) (map-concat as b f)

map-concat4 : {s t : Set} -> (a b c d : List s)
    -> (f : s -> t)
    -> map f (a ++ b ++ c ++ d) ≡ map f a ++ map f b ++ map f c ++ map f d
map-concat4 a b c d f =
    begin
        map f (a ++ b ++ c ++ d) 
    =⟨ map-concat a (b ++ c ++ d) f ⟩
        map f a ++ map f (b ++ c ++ d) 
    =⟨ cong (λ q -> map f a ++ q) (map-concat b (c ++ d) f) ⟩
        map f a ++ map f b ++ map f (c ++ d)
    =⟨ cong (λ q -> map f a ++ map f b ++ q) (map-concat c d f) ⟩
        map f a ++ map f b ++ map f c ++ map f d
    end

sum-concat : (a b : List Nat) -> sum (a ++ b) ≡ sum a + sum b
sum-concat [] b = refl
sum-concat (a ∷ as) b = 
    begin
        a + sum (as ++ b)
    =⟨ cong (λ q -> a + q) (sum-concat as b) ⟩
        a + (sum as + sum b)
    =⟨ sym $ add-assoc a (sum as) (sum b) ⟩
        sum (a ∷ as) + sum b
    end

sum-concat4 : (a b c d : List Nat) -> sum (a ++ b ++ c ++ d) ≡ sum a + sum b + sum c + sum d
sum-concat4 a b c d =
    begin
        sum (a ++ b ++ c ++ d) 
    =⟨ sum-concat a (b ++ c ++ d) ⟩
        sum a + sum (b ++ c ++ d) 
    =⟨ cong (λ q -> sum a + q) (sum-concat b (c ++ d)) ⟩
        sum a + (sum b + sum (c ++ d))
    =⟨ cong (λ q -> sum a + (sum b + q)) (sum-concat c d) ⟩
        sum a + (sum b + (sum c + sum d))
    =⟨ sym $ add-assoc (sum a) (sum b) (sum c + sum d) ⟩
        (sum a + sum b) + (sum c + sum d)
    =⟨ sym $ add-assoc (sum a + sum b) (sum c) (sum d) ⟩
        sum a + sum b + sum c + sum d
    end

nat-distributive : (a b c : Nat) -> (a * c) + (b * c) ≡ (a + b) * c
nat-distributive Z b c = refl
nat-distributive (S a) b c =
    begin
        (S a * c) + (b * c)
    =⟨ add-assoc c (a * c) (b * c) ⟩
        c + ((a * c) + b * c)
    =⟨ cong (_+_ c) (nat-distributive a b c) ⟩
        c + ((a + b) * c)
    =⟨⟩
        (S a + b) * c
    end

add-diff : (a b : Nat) -> IsTrue (a <= b) -> a + diff b a ≡ b
add-diff Z Z ab = refl
add-diff Z (S b) ab = refl
add-diff (S a) (S b) ab = cong S (add-diff a b ab)

line-split-left : (x1 xm x2 y : Nat) -> IsTrue (x1 <= xm) -> IsTrue (xm <= x2) -> IsTrue (x1 <= x2)
    -> diff xm x1 * y + diff x2 xm * y ≡ diff x2 x1 * y
line-split-left Z Z Z y x1m xm2 x12 = refl
line-split-left Z Z (S x2) y x1m xm2 x12 = refl
line-split-left Z (S xm) (S x2) y x1m xm2 x12 =
    begin
        (S xm) * y + diff (S x2) (S xm) * y
    =⟨ nat-distributive (S xm) (diff (S x2) (S xm)) y ⟩
        ((S xm) + diff (S x2) (S xm)) * y
    =⟨ cong (λ z → y + (z * y)) (add-diff xm x2 xm2) ⟩
        (S x2) * y
    end
line-split-left (S x1) (S xm) (S x2) y x1m xm2 x12 = line-split-left x1 xm x2 y x1m xm2 x12    

line-split-right : (x1 xm x2 y : Nat) -> IsTrue (x1 <= xm) -> IsTrue (xm <= x2) -> IsTrue (x1 <= x2)
    -> y * diff xm x1 + y * diff x2 xm ≡ y * diff x2 x1
line-split-right x1 xm x2 y x1m xm2 x12 =
    begin
        y * diff xm x1 + y * diff x2 xm
    =⟨ cong2 _+_ (mul-comm y (diff xm x1)) (mul-comm y (diff x2 xm)) ⟩
        diff xm x1 * y + diff x2 xm * y
    =⟨ line-split-left x1 xm x2 y x1m xm2 x12 ⟩
        diff x2 x1 * y
    =⟨ mul-comm (diff x2 x1) y ⟩
        y * diff x2 x1
    end

square-split : (x1 y1 xm ym x2 y2 : Nat) -> IsTrue (x1 <= xm) -> IsTrue (xm <= x2) -> IsTrue (y1 <= ym) -> IsTrue (ym <= y2)
    -> diff xm x1 * diff ym y1 + diff x2 xm * diff ym y1 + diff xm x1 * diff y2 ym + diff x2 xm * diff y2 ym ≡ diff x2 x1 * diff y2 y1
square-split x1 y1 xm ym x2 y2 x1m xm2 y1m ym2 =
    begin
        diff xm x1 * diff ym y1 + diff x2 xm * diff ym y1 + diff xm x1 * diff y2 ym + diff x2 xm * diff y2 ym
    =⟨ add-assoc ((diff xm x1 * diff ym y1) + (diff x2 xm * diff ym y1)) (diff xm x1 * diff y2 ym) (diff x2 xm * diff y2 ym) ⟩
        (diff xm x1 * diff ym y1 + diff x2 xm * diff ym y1) + (diff xm x1 * diff y2 ym + diff x2 xm * diff y2 ym)
    =⟨ cong2 _+_ 
        (line-split-left x1 xm x2 (diff ym y1) x1m xm2 (lteTransitive x1 xm x2 x1m xm2)) 
        (line-split-left x1 xm x2 (diff y2 ym) x1m xm2 (lteTransitive x1 xm x2 x1m xm2)) ⟩
        (diff x2 x1 * diff ym y1) + (diff x2 x1 * diff y2 ym)
    =⟨ line-split-right y1 ym y2 (diff x2 x1) y1m ym2 (lteTransitive y1 ym y2 y1m ym2) ⟩
        diff x2 x1 * diff y2 y1
    end

min-comb : (a b c : Nat) -> IsTrue (a <= b) -> IsTrue (a <= c) -> IsTrue (a <= min b c)
min-comb a b c ab ac = useEq (sym $
    begin
        a <= min b c
    =⟨ sym $ propFnIf {c = c < b} (_<=_ a) ⟩
        (if _ then a <= c else a <= b)
    =⟨ cong2 (if_then_else_ _) (isTrueToEquiv ac) (isTrueToEquiv ab)  ⟩
        (if _ then true else true)
    =⟨ propIfBranchesSame true ⟩
        true
    end) IsTrue.itsTrue

min-rel-1 : (x1 mid x2 : Nat) -> IsTrue (x1 <= x2) -> IsTrue (x1 <= min x2 (mid + x1))
min-rel-1 x1 mid x2 x12 = min-comb x1 x2 (mid + x1) x12 (lteSumOne x1 x1 mid (lteSelf x1))

min-rel-2 : (a b : Nat) -> IsTrue (min a b <= a)
min-rel-2 a b = {!   !}

length-tilesQd : {t : Set} {{eqT : Eq t}} {dep : Nat} -> (vqd : VQuadrant t {dep})
    -> (x1 y1 x2 y2 : Nat) -> IsTrue (x1 <= x2) -> IsTrue (y1 <= y2)
    -> sum (map lengthₙ (map expand (tilesQd dep vqd (RegionC (x1 , y1) (x2 , y2))))) ≡ diff x2 x1 * diff y2 y1
length-tilesQd {t} {dep = dep} (CVQuadrant (Leaf v) {p}) x1 y1 x2 y2 _ _ =
    begin
        sum (map lengthₙ (map expand (tilesQd dep (CVQuadrant (Leaf v) {p}) (RegionC (x1 , y1) (x2 , y2)))))
    =⟨⟩
        lengthₙ (replicateₙ (diff x2 x1 * diff y2 y1) v) + 0
    =⟨ add-comm _ 0 ⟩
        lengthₙ (replicateₙ (diff x2 x1 * diff y2 y1) v)
    =⟨ length-replicateₙ (diff x2 x1 * diff y2 y1) v ⟩
        diff x2 x1 * diff y2 y1
    end
length-tilesQd {dep = S dep} (CVQuadrant (Node a b c d) {p}) x1 y1 x2 y2 xp yp =
    begin
        sum (map lengthₙ (map expand (tilesQd (S dep) (CVQuadrant (Node a b c d) {p}) (RegionC (x1 , y1) (x2 , y2)))))
    =⟨⟩
        sum (map lengthₙ (map expand (ca ++ cb ++ cc ++ cd)))
    =⟨ cong (λ q -> sum (map lengthₙ q)) (map-concat4 ca cb cc cd expand) ⟩
        sum (map lengthₙ (map expand ca  ++ map expand cb ++ map expand cc ++ map expand cd))
    =⟨ cong sum (map-concat4 (map expand ca) (map expand cb) (map expand cc) (map expand cd) lengthₙ) ⟩
        sum (map lengthₙ (map expand ca) ++ map lengthₙ (map expand cb) ++ map lengthₙ (map expand cc) ++ map lengthₙ (map expand cd))
    =⟨ sum-concat4 (map lengthₙ (map expand ca)) (map lengthₙ (map expand cb)) (map lengthₙ (map expand cc)) (map lengthₙ (map expand cd)) ⟩
        sum (map lengthₙ (map expand ca)) + sum (map lengthₙ (map expand cb)) + sum (map lengthₙ (map expand cc)) + sum (map lengthₙ (map expand cd))
    =⟨ {!   !} ⟩
          diff (min x2 (mid + x1)) x1 * diff (min y2 (mid + y1)) y1 
        + diff x2 (min x2 (mid + x1)) * diff (min y2 (mid + y1)) y1  
        + diff (min x2 (mid + x1)) x1 * diff y2 (min y2 (mid + y1))
        + diff x2 (min x2 (mid + x1)) * diff y2 (min y2 (mid + y1))
    =⟨ square-split x1 y1 (min x2 (mid + x1)) (min y2 (mid + y1)) x2 y2 (min-rel-1 x1 mid x2 xp) (min-rel-2 x2 (mid + x1)) (min-rel-1 y1 mid y2 yp) (min-rel-2 y2 (mid + y1)) ⟩
        diff x2 x1 * diff y2 y1
    end where
        mid = pow 2 dep
        ca = tilesQd dep (CVQuadrant a) (RegionC (x1 , y1) (min x2 (mid + x1) , min y2 (mid + y1)) )
        cb = tilesQd dep (CVQuadrant b) (RegionC (min x2 (mid + x1) , y1) (x2 , min y2 (mid + y1)) )
        cc = tilesQd dep (CVQuadrant c) (RegionC (x1 , min y2 (mid + y1)) (min x2 (mid + x1) , y2) )
        cd = tilesQd dep (CVQuadrant d) (RegionC (min x2 (mid + x1) , min y2 (mid + y1)) (x2 , y2) )

proof-length : {t : Set} {{eqT : Eq t}} {dep : Nat} -> (vqt : VQuadTree t {dep}) -> lengthₑ (quadtreeFoldable dep) vqt ≡ size vqt
proof-length {t} ⦃ eqT ⦄ {dep} vqt@(CVQuadTree (Wrapper (w , h) qd) {p1} {p2}) =
    begin
        lengthₑ (quadtreeFoldable dep) vqt
    =⟨⟩
        lengthₙ (concat (map expand (tilesQd dep (CVQuadrant qd {p1}) (RegionC (0 , 0) (w , h)))))
    =⟨ length-concat (map expand (tilesQd dep (CVQuadrant qd {p1}) (RegionC (0 , 0) (w , h)))) ⟩
        sum (map lengthₙ (map expand (tilesQd dep (CVQuadrant qd {p1}) (RegionC (0 , 0) (w , h)))))
    =⟨ length-tilesQd {dep = dep} (CVQuadrant qd {p1}) 0 0 w h (zeroLteAny w) (zeroLteAny h) ⟩
        w * h
    end