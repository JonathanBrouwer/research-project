module Data.QuadTree.FoldableProofs.FoldableFunctorProof where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Logic
open import Data.QuadTree.Implementation.Definition
open import Data.QuadTree.Implementation.ValidTypes
open import Data.QuadTree.Implementation.QuadrantLenses
open import Data.QuadTree.Implementation.SafeFunctions
open import Data.QuadTree.Implementation.PropDepthRelation
open import Data.QuadTree.Implementation.Foldable
open import Data.QuadTree.Implementation.Functors
open import Data.QuadTree.FoldableProofs.FoldableProof
open import Data.QuadTree.FunctorProofs.Valid-QuadrantFunctor

proof-foldfmap-list : {t s : Set} {{monT : Monoid t}} {{monS : Monoid s}} -> (l : List t )
    -> (f : t -> s)
    -> foldMap f l ≡ foldMap id (fmap f l)
proof-foldfmap-list [] f = refl
proof-foldfmap-list (x ∷ xs) f =
    begin
        f x <> foldMap f xs
    =⟨ cong (_<>_ (f x)) (proof-foldfmap-list xs f) ⟩
        f x <> foldMap id (fmap f xs)
    end

fmap-replicate : {A B : Set} -> (f : A -> B) -> (v : A) -> (n : Nat)
    -> fmap f (replicateₙ n v) ≡ replicateₙ n (f v)
fmap-replicate f v Z = refl
fmap-replicate f v (S n) = cong (λ z → f v ∷ z) (fmap-replicate f v n)

fmap-concat : {A B : Set} -> (f : A -> B) -> (l1 l2 : List A)
    -> fmap f (l1 ++ l2) ≡ fmap f l1 ++ fmap f l2
fmap-concat f [] l2 = refl
fmap-concat f (x ∷ l1) l2 = cong (λ z → f x ∷ z) (fmap-concat f l1 l2)

fmap-concat4 : {A B : Set} -> (f : A -> B) -> (l1 l2 l3 l4 : List A)
    -> fmap f (l1 ++ l2 ++ l3 ++ l4) ≡ fmap f l1 ++ fmap f l2 ++ fmap f l3 ++ fmap f l4
fmap-concat4 f l1 l2 l3 l4 =
    begin
        fmap f (l1 ++ l2 ++ l3 ++ l4)
    =⟨ fmap-concat f l1 (l2 ++ l3 ++ l4) ⟩
        fmap f l1 ++ fmap f (l2 ++ l3 ++ l4)
    =⟨ cong (_++_ (map f l1)) (fmap-concat f l2 (l3 ++ l4)) ⟩
        fmap f l1 ++ fmap f l2 ++ fmap f (l3 ++ l4)
    =⟨ cong (λ z → map f l1 ++ map f l2 ++ z) (fmap-concat f l3 l4) ⟩
        fmap f l1 ++ fmap f l2 ++ fmap f l3 ++ fmap f l4
    end

fmap-expand : {A B : Set} {{eqA : Eq A}} {{eqB : Eq B}} -> (f : A -> B) -> (t : Tile A)
    -> fmap f (expand t) ≡ expand (fmap f t)
fmap-expand f t@(TileC v (RegionC (x1 , y1) (x2 , y2))) = fmap-replicate f v (diff x2 x1 * diff y2 y1)

fmap-concat-expand : {A B : Set} {{eqA : Eq A}} {{eqB : Eq B}} -> (f : A -> B) -> (l : List (Tile A))
    -> (fmap f $ concat $ map expand l) ≡ (concat $ map expand $ fmap (fmap f) l) 
fmap-concat-expand f [] = refl
fmap-concat-expand f (x ∷ xs) =
    begin
        fmap f (expand x ++ concat (map expand xs))
    =⟨ fmap-concat f (expand x) _ ⟩
        fmap f (expand x) ++ fmap f (concat (map expand xs))
    =⟨ cong (_++_ (fmap f (expand x))) (fmap-concat-expand f xs) ⟩
        fmap f (expand x) ++ concat (map expand $ fmap (fmap f) xs)
    =⟨ cong (λ q -> q ++ concat (map expand $ fmap (fmap f) xs)) (fmap-expand f x) ⟩
        expand (fmap f x) ++ concat (map expand $ fmap (fmap f) xs)
    end

replicate-concat : {t : Set} -> (a b : Nat) -> (v : t)
    -> replicateₙ a v ++ replicateₙ b v ≡ replicateₙ (a + b) v
replicate-concat Z b v = refl
replicate-concat (S a) b v = cong (λ z → v ∷ z) (replicate-concat a b v)

replicate-concat4 : {t : Set} -> (a b c d : Nat) -> (v : t)
    -> replicateₙ a v ++ replicateₙ b v ++ replicateₙ c v ++ replicateₙ d v ≡ replicateₙ (a + b + c + d) v
replicate-concat4 a b c d v =
    begin
        replicateₙ a v ++ replicateₙ b v ++ (replicateₙ c v ++ replicateₙ d v)
    =⟨ cong (λ z → replicateₙ a v ++ replicateₙ b v ++ z) (replicate-concat c d v) ⟩
        replicateₙ a v ++ replicateₙ b v ++ replicateₙ (c + d) v
    =⟨ cong (_++_ (replicateₙ a v)) (replicate-concat b (c + d) v) ⟩
        replicateₙ a v ++ replicateₙ (b + (c + d)) v
    =⟨ replicate-concat a (b + (c + d)) v ⟩
        replicateₙ (a + (b + (c + d))) v
    =⟨ sym (cong (λ z → replicateₙ z v) (add-assoc a b (c + d))) ⟩
        replicateₙ (a + b + (c + d)) v
    =⟨ sym (cong (λ z → replicateₙ z v) (add-assoc (a + b) c d)) ⟩
        replicateₙ (a + b + c + d) v
    end

++-assoc : {t : Set} -> (l1 l2 l3 : List t)
    -> (l1 ++ l2) ++ l3 ≡ l1 ++ (l2 ++ l3)
++-assoc [] l2 l3 = refl
++-assoc (x ∷ xs) l2 l3 = cong (λ z → x ∷ z) (++-assoc xs l2 l3)

concat-cme : {t : Set} -> (l1 l2 : List (Tile t))
    -> concat (map expand (l1 ++ l2)) ≡ (concat $ map expand l1) ++ (concat $ map expand l2)
concat-cme [] l2 = refl
concat-cme l1@(x ∷ xs) l2 = 
    begin
        expand x ++ concat (map expand (xs ++ l2))
    =⟨ cong (_++_ (expand x)) (concat-cme xs l2) ⟩
        expand x ++ ((concat $ map expand xs) ++ (concat $ map expand l2))
    =⟨ sym $ ++-assoc (expand x) (concat $ map expand xs) (concat $ map expand l2) ⟩
        (expand x ++ concat (map expand xs)) ++ concat (map expand l2)
    end

concat-cme4 : {t : Set} -> (l1 l2 l3 l4 : List (Tile t))
    -> concat (map expand (l1 ++ l2 ++ l3 ++ l4)) ≡ (concat (map expand l1)) ++ (concat (map expand l2)) ++ (concat (map expand l3)) ++ (concat (map expand l4))
concat-cme4 l1 l2 l3 l4 =
    begin 
        concat (map expand (l1 ++ (l2 ++ (l3 ++ l4))))
    =⟨ concat-cme l1 (l2 ++ (l3 ++ l4)) ⟩
        concat (map expand l1) ++ concat (map expand (l2 ++ (l3 ++ l4)))
    =⟨ cong (_++_ (concat (map expand l1))) (concat-cme l2 (l3 ++ l4)) ⟩
        concat (map expand l1) ++ concat (map expand l2) ++ concat (map expand (l3 ++ l4))
    =⟨ cong (λ q -> concat (map expand l1) ++ concat (map expand l2) ++ q) (concat-cme l3 l4) ⟩
        concat (map expand l1) ++ concat (map expand l2) ++ concat (map expand l3) ++ concat (map expand l4)
    end

tilesQd-concat : {A : Set} {{eqA : Eq A}} -> (deps : Nat) -> (a b c d : VQuadrant A {deps}) -> (x1 y1 x2 y2 : Nat)
    -> IsTrue (x1 <= x2) -> IsTrue (y1 <= y2)
    -> ({a b : A} -> IsTrue (a == b) -> a ≡ b)
    -> (concat $ map expand $ (tilesQd deps a (RegionC (x1 , y1) (min x2 (pow 2 deps + x1) , min y2 (pow 2 deps + y1)))
        ++ tilesQd deps b (RegionC (min x2 (pow 2 deps + x1) , y1) (x2 , min y2 (pow 2 deps + y1)))
        ++ tilesQd deps c (RegionC (x1 , min y2 (pow 2 deps + y1)) (min x2 (pow 2 deps + x1) , y2) )
        ++ tilesQd deps d (RegionC (min x2 (pow 2 deps + x1) , min y2 (pow 2 deps + y1)) (x2 , y2) )))
    ≡ (concat $ map expand $ tilesQd (S deps) (combine a b c d) (RegionC (x1 , y1) (x2 , y2)))
tilesQd-concat {A} deps a@(CVQuadrant (Leaf va)) b@(CVQuadrant (Leaf vb)) c@(CVQuadrant (Leaf vc)) d@(CVQuadrant (Leaf vd)) x1 y1 x2 y2 xp yp peq =
    ifc (va == vb && vb == vc && vc == vd) 
    then (λ {{pc}} ->
        begin
            (cme $ TileC va rA ∷ TileC vb rB ∷ TileC vc rC ∷ TileC vd rD ∷ [])
        =⟨⟩
            replicateₙ (area rA) va ++ replicateₙ (area rB) vb ++ replicateₙ (area rC) vc ++ replicateₙ (area rD) vd ++ []
        =⟨ cong (λ q -> replicateₙ (area rA) va ++ replicateₙ (area rB) vb ++ replicateₙ (area rC) vc ++ q) (concat-nothing _) ⟩
            replicateₙ (area rA) (va) ++ replicateₙ (area rB) (vb) ++ replicateₙ (area rC) (vc) ++ replicateₙ (area rD) vd
        =⟨ cong (λ v -> replicateₙ (area rA) (va) ++ replicateₙ (area rB) (vb) ++ replicateₙ (area rC) (vc) ++ replicateₙ (area rD) v) 
            (sym $ peq $ andSnd {vb == vc} $ andSnd {va == vb} pc) ⟩  
            replicateₙ (area rA) (va) ++ replicateₙ (area rB) (vb) ++ replicateₙ (area rC) (vc) ++ replicateₙ (area rD) (vc)
        =⟨ cong (λ v -> replicateₙ (area rA) (va) ++ replicateₙ (area rB) (vb) ++ replicateₙ (area rC) (v) ++ replicateₙ (area rD) (v)) 
            (sym $ peq $ andFst {vb == vc} $ andSnd {va == vb} pc) ⟩
            replicateₙ (area rA) (va) ++ replicateₙ (area rB) (vb) ++ replicateₙ (area rC) (vb) ++ replicateₙ (area rD) (vb)
        =⟨ cong (λ v -> replicateₙ (area rA) (va) ++ replicateₙ (area rB) (v) ++ replicateₙ (area rC) (v) ++ replicateₙ (area rD) (v)) 
            (sym $ peq $ andFst {va == vb} pc) ⟩
            replicateₙ (area rA) (va) ++ replicateₙ (area rB) (va) ++ replicateₙ (area rC) (va) ++ replicateₙ (area rD) (va)
        =⟨ replicate-concat4 (area rA) (area rB) (area rC) (area rD) (va) ⟩
            replicateₙ (area rA + area rB + area rC + area rD) (va)
        =⟨ cong (λ q -> replicateₙ q (va)) (square-split x1 y1 (min x2 (mid + x1)) (min y2 (mid + y1)) x2 y2 
            (min-rel-1 x1 mid x2 xp) (min-rel-2 x2 (mid + x1)) (min-rel-1 y1 mid y2 yp) (min-rel-2 y2 (mid + y1))) ⟩
            replicateₙ (diff x2 x1 * diff y2 y1) (va)
        =⟨ sym $ concat-nothing (replicateₙ (diff x2 x1 * diff y2 y1) (va)) ⟩
            replicateₙ (diff x2 x1 * diff y2 y1) va ++ []
        =⟨⟩
            (cme $ TileC va (RegionC (x1 , y1) (x2 , y2)) ∷ [])
        =⟨ cong (λ q -> cme $ tilesQd (S deps) q (RegionC (x1 , y1) (x2 , y2))) (sym $ ifcTrue (va == vb && vb == vc && vc == vd) pc) ⟩
            (cme $ tilesQd (S deps) (ifc (va == vb && vb == vc && vc == vd) then CVQuadrant (Leaf va) else CVQuadrant (Node (Leaf va) (Leaf vb) (Leaf vc) (Leaf vd))) (RegionC (x1 , y1) (x2 , y2)))
        end) 
    else (λ {{pc}} -> 
        begin
            (concat $ map expand $ tilesQd (S deps) (CVQuadrant (Node (Leaf va) (Leaf vb) (Leaf vc) (Leaf vd)) {andCombine (zeroLteAny deps) (falseToNotTrue pc)}) (RegionC (x1 , y1) (x2 , y2)))
        =⟨ cong {x = CVQuadrant (Node (Leaf va) (Leaf vb) (Leaf vc) (Leaf vd)) {andCombine (zeroLteAny deps) (falseToNotTrue pc)}} (λ q -> concat $ map expand $  tilesQd (S deps) q (RegionC (x1 , y1) (x2 , y2))) (sym $ ifcFalse (va == vb && vb == vc && vc == vd) pc) ⟩
            (concat $ map expand $ tilesQd (S deps) (ifc (va == vb && vb == vc && vc == vd) then CVQuadrant (Leaf va) else CVQuadrant (Node (Leaf va) (Leaf vb) (Leaf vc) (Leaf vd))) (RegionC (x1 , y1) (x2 , y2)))
        end) where
        mid = pow 2 deps
        rA = (RegionC (x1 , y1) (min x2 (mid + x1) , min y2 (mid + y1)))
        rB = (RegionC (min x2 (mid + x1) , y1) (x2 , min y2 (mid + y1)))
        rC = (RegionC (x1 , min y2 (mid + y1)) (min x2 (mid + x1) , y2) )
        rD = (RegionC (min x2 (mid + x1) , min y2 (mid + y1)) (x2 , y2) )
        cme : List (Tile A) -> List A
        cme v = concat $ map expand $ v
        area : Region -> Nat
        area (RegionC (x1 , y1) (x2 , y2)) = diff x2 x1 * diff y2 y1
tilesQd-concat deps (CVQuadrant (Leaf x)) (CVQuadrant (Leaf x₁)) (CVQuadrant (Leaf x₂)) (CVQuadrant (Node d d₁ d₂ d₃)) x1 y1 x2 y2 xp yp peq = refl
tilesQd-concat deps (CVQuadrant (Leaf x)) (CVQuadrant (Leaf x₁)) (CVQuadrant (Node c c₁ c₂ c₃)) (CVQuadrant d) x1 y1 x2 y2 xp yp peq = refl
tilesQd-concat deps (CVQuadrant (Leaf x)) (CVQuadrant (Node b b₁ b₂ b₃)) (CVQuadrant c) (CVQuadrant d) x1 y1 x2 y2 xp yp peq = refl
tilesQd-concat deps (CVQuadrant (Node a a₁ a₂ a₃)) (CVQuadrant b) (CVQuadrant c) (CVQuadrant d) x1 y1 x2 y2 xp yp peq = refl


fmap-tilesQd : {A B : Set} {{eqA : Eq A}} {{eqB : Eq B}} -> (f : A -> B) -> (dep : Nat) -> (vqd : VQuadrant A {dep}) -> (x1 y1 x2 y2 : Nat)
    -> IsTrue (x1 <= x2) -> IsTrue (y1 <= y2)
    -> ({a b : A} -> IsTrue (a == b) -> a ≡ b)
    -> ({a b : B} -> IsTrue (a == b) -> a ≡ b)
    -> (concat $ map expand $ fmap (fmap f) $ tilesQd dep vqd (RegionC (x1 , y1) (x2 , y2))) ≡ (concat $ map expand $ tilesQd dep (fmapₑ (quadrantFunctor dep) f vqd) (RegionC (x1 , y1) (x2 , y2)))
fmap-tilesQd f dep (CVQuadrant (Leaf v) {p1}) x1 y1 x2 y2 px py peqA peqB = refl
fmap-tilesQd {A} {B} f dep@(S deps) vqd@(CVQuadrant (Node a@(Leaf va) b@(Leaf vb) c@(Leaf vc) d@(Leaf vd)) {p1}) x1 y1 x2 y2 xp yp peqA peqB =
    ifc ((va == vb) && (vb == vc) && (vc == vd))
    then (λ {{pc}} -> 
        (begin
            (cme $ fmap (fmap f) $ tilesQd dep vqd reg)
        =⟨⟩
            (cme $ TileC (f va) rA ∷ TileC (f vb) rB ∷ TileC (f vc) rC ∷ TileC (f vd) rD ∷ [])
        =⟨⟩
            replicateₙ (area rA) (f va) ++ replicateₙ (area rB) (f vb) ++ replicateₙ (area rC) (f vc) ++ replicateₙ (area rD) (f vd) ++ []
        =⟨ cong (λ q -> replicateₙ (area rA) (f va) ++ replicateₙ (area rB) (f vb) ++ replicateₙ (area rC) (f vc) ++ q) (concat-nothing _) ⟩
            replicateₙ (area rA) (f va) ++ replicateₙ (area rB) (f vb) ++ replicateₙ (area rC) (f vc) ++ replicateₙ (area rD) (f vd)
        =⟨ cong (λ v -> replicateₙ (area rA) (f va) ++ replicateₙ (area rB) (f vb) ++ replicateₙ (area rC) (f vc) ++ replicateₙ (area rD) (f v)) 
            (sym $ peqA $ andSnd {vb == vc} $ andSnd {va == vb} pc) ⟩  
            replicateₙ (area rA) (f va) ++ replicateₙ (area rB) (f vb) ++ replicateₙ (area rC) (f vc) ++ replicateₙ (area rD) (f vc)
        =⟨ cong (λ v -> replicateₙ (area rA) (f va) ++ replicateₙ (area rB) (f vb) ++ replicateₙ (area rC) (f v) ++ replicateₙ (area rD) (f v)) 
            (sym $ peqA $ andFst {vb == vc} $ andSnd {va == vb} pc) ⟩
            replicateₙ (area rA) (f va) ++ replicateₙ (area rB) (f vb) ++ replicateₙ (area rC) (f vb) ++ replicateₙ (area rD) (f vb)
        =⟨ cong (λ v -> replicateₙ (area rA) (f va) ++ replicateₙ (area rB) (f v) ++ replicateₙ (area rC) (f v) ++ replicateₙ (area rD) (f v)) 
            (sym $ peqA $ andFst {va == vb} pc) ⟩
            replicateₙ (area rA) (f va) ++ replicateₙ (area rB) (f va) ++ replicateₙ (area rC) (f va) ++ replicateₙ (area rD) (f va)
        =⟨ replicate-concat4 (area rA) (area rB) (area rC) (area rD) (f va) ⟩
            replicateₙ (area rA + area rB + area rC + area rD) (f va)
        =⟨ cong (λ q -> replicateₙ q (f va)) (square-split x1 y1 (min x2 (mid + x1)) (min y2 (mid + y1)) x2 y2 
            (min-rel-1 x1 mid x2 xp) (min-rel-2 x2 (mid + x1)) (min-rel-1 y1 mid y2 yp) (min-rel-2 y2 (mid + y1))) ⟩
            replicateₙ (diff x2 x1 * diff y2 y1) (f va)
        =⟨ sym $ concat-nothing (replicateₙ (diff x2 x1 * diff y2 y1) (f va)) ⟩
            replicateₙ (diff x2 x1 * diff y2 y1) (f va) ++ []
        =⟨ cong (λ q -> cme $ tilesQd dep q reg) 
                (sym $ ifcTrue ((f va == f vb) && (f vb == f vc) && (f vc == f vd)) 
                    (useEq (cong3 (λ e1 e2 e3 -> e1 && e2 && e3) (eq-subst f va vb) (eq-subst f vb vc) (eq-subst f vc vd)) pc)) ⟩
            (cme $ tilesQd dep (combine 
                (fmapₑ (quadrantFunctor deps) f sA) 
                (fmapₑ (quadrantFunctor deps) f sB) 
                (fmapₑ (quadrantFunctor deps) f sC) 
                (fmapₑ (quadrantFunctor deps) f sD)) reg)
        =⟨⟩
            (cme $ tilesQd dep (fmapₑ (quadrantFunctor dep) f vqd) reg)
        end))
    else (λ {{pc}} -> 
        (begin
            (cme $ fmap (fmap f) $ tilesQd dep vqd reg)
        =⟨⟩
            (cme $ TileC (f va) rA ∷ TileC (f vb) rB ∷ TileC (f vc) rC ∷ TileC (f vd) rD ∷ [])
        =⟨⟩
            (cme $ tilesQd dep (CVQuadrant (Node (Leaf (f va)) (Leaf (f vb)) (Leaf (f vc)) (Leaf (f vd))) 
                {andCombine (zeroLteAny deps) (falseToNotTrue $ useEqFalse (cong3 (λ e1 e2 e3 -> e1 && e2 && e3) (eq-subst f va vb) (eq-subst f vb vc) (eq-subst f vc vd)) pc)}) reg)
        =⟨ cong {x = CVQuadrant (Node (Leaf (f va)) (Leaf (f vb)) (Leaf (f vc)) (Leaf (f vd))) 
                {andCombine (zeroLteAny deps) (falseToNotTrue $ useEqFalse (cong3 (λ e1 e2 e3 -> e1 && e2 && e3) (eq-subst f va vb) (eq-subst f vb vc) (eq-subst f vc vd)) pc)}}
             (λ q -> cme $ tilesQd dep q reg) (sym $ ifcFalse ((f va == f vb) && (f vb == f vc) && (f vc == f vd))
             (useEqFalse (cong3 (λ e1 e2 e3 -> e1 && e2 && e3) (eq-subst f va vb) (eq-subst f vb vc) (eq-subst f vc vd)) pc)) ⟩
            (cme $ tilesQd dep (combine 
                (fmapₑ (quadrantFunctor deps) f sA) 
                (fmapₑ (quadrantFunctor deps) f sB) 
                (fmapₑ (quadrantFunctor deps) f sC) 
                (fmapₑ (quadrantFunctor deps) f sD)) reg)
        =⟨⟩
            (cme $ tilesQd dep (fmapₑ (quadrantFunctor dep) f vqd) reg)
        end))
    
    where
        mid = pow 2 deps
        rA = (RegionC (x1 , y1) (min x2 (mid + x1) , min y2 (mid + y1)))
        rB = (RegionC (min x2 (mid + x1) , y1) (x2 , min y2 (mid + y1)))
        rC = (RegionC (x1 , min y2 (mid + y1)) (min x2 (mid + x1) , y2) )
        rD = (RegionC (min x2 (mid + x1) , min y2 (mid + y1)) (x2 , y2) )
        reg = (RegionC (x1 , y1) (x2 , y2))
        sA = CVQuadrant {dep = deps} a {aSub {dep = deps} a b c d p1}
        sB = CVQuadrant {dep = deps} b {bSub {dep = deps} a b c d p1}
        sC = CVQuadrant {dep = deps} c {cSub {dep = deps} a b c d p1}
        sD = CVQuadrant {dep = deps} d {dSub {dep = deps} a b c d p1}
        cme : List (Tile B) -> List B
        cme v = concat $ map expand $ v
        area : Region -> Nat
        area (RegionC (x1 , y1) (x2 , y2)) = diff x2 x1 * diff y2 y1
fmap-tilesQd {A} {B} f dep@(S deps) vqd@(CVQuadrant (Node a@(Leaf _) b@(Leaf _) c@(Leaf _) d@(Node _ _ _ _)) {p1}) x1 y1 x2 y2 xp yp peqA peqB =
    begin
        (cme $ fmap (fmap f) $ tilesQd dep vqd reg)
    =⟨⟩
        (cme $ fmap (fmap f) $ (
            tilesQd deps sA rA ++ tilesQd deps sB rB ++ tilesQd deps sC rC ++ tilesQd deps sD rD
        ))
    =⟨ cong cme $ fmap-concat4 (fmap f) (tilesQd deps sA rA) (tilesQd deps sB rB) (tilesQd deps sC rC) (tilesQd deps sD rD) ⟩
        (cme (
            fmap (fmap f) (tilesQd deps sA rA) 
            ++ fmap (fmap f) (tilesQd deps sB rB)
            ++ fmap (fmap f) (tilesQd deps sC rC)
            ++ fmap (fmap f) (tilesQd deps sD rD)
        ))
    =⟨ concat-cme4 (fmap (fmap f) (tilesQd deps sA rA)) (fmap (fmap f) (tilesQd deps sB rB)) (fmap (fmap f) (tilesQd deps sC rC)) (fmap (fmap f) (tilesQd deps sD rD)) ⟩
        (cme $ fmap (fmap f) (tilesQd deps sA rA))
        ++ (cme $ fmap (fmap f) (tilesQd deps sB rB))
        ++ (cme $ fmap (fmap f) (tilesQd deps sC rC))
        ++ (cme $ fmap (fmap f) (tilesQd deps sD rD))
    =⟨ cong4 (λ l1 l2 l3 l4 -> l1 ++ l2 ++ l3 ++ l4) 
        (fmap-tilesQd f deps sA x1 y1 (min x2 (mid + x1)) (min y2 (mid + y1)) (min-rel-1 x1 mid x2 xp) (min-rel-1 y1 mid y2 yp) peqA peqB) 
        (fmap-tilesQd f deps sB (min x2 (mid + x1)) y1 x2 (min y2 (mid + y1)) (min-rel-2 x2 (mid + x1)) (min-rel-1 y1 mid y2 yp) peqA peqB) 
        (fmap-tilesQd f deps sC x1 (min y2 (mid + y1)) (min x2 (mid + x1)) y2 (min-rel-1 x1 mid x2 xp) (min-rel-2 y2 (mid + y1)) peqA peqB) 
        (fmap-tilesQd f deps sD (min x2 (mid + x1)) (min y2 (mid + y1)) x2 y2 (min-rel-2 x2 (mid + x1)) (min-rel-2 y2 (mid + y1)) peqA peqB) ⟩

        (cme $ (tilesQd deps (fmapₑ (quadrantFunctor deps) f sA) rA))
        ++ (cme $ (tilesQd deps (fmapₑ (quadrantFunctor deps) f sB) rB))
        ++ (cme $ (tilesQd deps (fmapₑ (quadrantFunctor deps) f sC) rC))
        ++ (cme $ (tilesQd deps (fmapₑ (quadrantFunctor deps) f sD) rD))
    =⟨ sym $ concat-cme4 (tilesQd deps (fmapₑ (quadrantFunctor deps) f sA) rA) (tilesQd deps (fmapₑ (quadrantFunctor deps) f sB) rB) (tilesQd deps (fmapₑ (quadrantFunctor deps) f sC) rC) (tilesQd deps (fmapₑ (quadrantFunctor deps) f sD) rD) ⟩
        (cme (
            tilesQd deps (fmapₑ (quadrantFunctor deps) f sA) rA
            ++ tilesQd deps (fmapₑ (quadrantFunctor deps) f sB) rB
            ++ tilesQd deps (fmapₑ (quadrantFunctor deps) f sC) rC
            ++ tilesQd deps (fmapₑ (quadrantFunctor deps) f sD) rD
        ))
    =⟨ tilesQd-concat deps (fmapₑ (quadrantFunctor deps) f sA) (fmapₑ (quadrantFunctor deps) f sB) (fmapₑ (quadrantFunctor deps) f sC) (fmapₑ (quadrantFunctor deps) f sD) x1 y1 x2 y2 xp yp peqB ⟩
        (cme $ tilesQd dep 
            (combine (fmapₑ (quadrantFunctor deps) f sA) (fmapₑ (quadrantFunctor deps) f sB) (fmapₑ (quadrantFunctor deps) f sC) (fmapₑ (quadrantFunctor deps) f sD)) reg)
    =⟨⟩
        (cme $ tilesQd dep (fmapₑ (quadrantFunctor dep) f vqd) reg)
    end where
        cme : List (Tile B) -> List B
        cme v = concat $ map expand $ v
        reg = (RegionC (x1 , y1) (x2 , y2))
        mid = pow 2 deps
        rA = (RegionC (x1 , y1) (min x2 (mid + x1) , min y2 (mid + y1)))
        rB = (RegionC (min x2 (mid + x1) , y1) (x2 , min y2 (mid + y1)))
        rC = (RegionC (x1 , min y2 (mid + y1)) (min x2 (mid + x1) , y2) )
        rD = (RegionC (min x2 (mid + x1) , min y2 (mid + y1)) (x2 , y2) )
        sA = CVQuadrant {dep = deps} a {aSub {dep = deps} a b c d p1}
        sB = CVQuadrant {dep = deps} b {bSub {dep = deps} a b c d p1}
        sC = CVQuadrant {dep = deps} c {cSub {dep = deps} a b c d p1}
        sD = CVQuadrant {dep = deps} d {dSub {dep = deps} a b c d p1}
fmap-tilesQd {A} {B} f dep@(S deps) vqd@(CVQuadrant (Node a@(Leaf _) b@(Leaf _) c@(Node _ _ _ _) d) {p1}) x1 y1 x2 y2 xp yp peqA peqB =
    begin
        (cme $ fmap (fmap f) $ tilesQd dep vqd reg)
    =⟨⟩
        (cme $ fmap (fmap f) $ (
            tilesQd deps sA rA ++ tilesQd deps sB rB ++ tilesQd deps sC rC ++ tilesQd deps sD rD
        ))
    =⟨ cong cme $ fmap-concat4 (fmap f) (tilesQd deps sA rA) (tilesQd deps sB rB) (tilesQd deps sC rC) (tilesQd deps sD rD) ⟩
        (cme (
            fmap (fmap f) (tilesQd deps sA rA) 
            ++ fmap (fmap f) (tilesQd deps sB rB)
            ++ fmap (fmap f) (tilesQd deps sC rC)
            ++ fmap (fmap f) (tilesQd deps sD rD)
        ))
    =⟨ concat-cme4 (fmap (fmap f) (tilesQd deps sA rA)) (fmap (fmap f) (tilesQd deps sB rB)) (fmap (fmap f) (tilesQd deps sC rC)) _ ⟩
        (cme $ fmap (fmap f) (tilesQd deps sA rA))
        ++ (cme $ fmap (fmap f) (tilesQd deps sB rB))
        ++ (cme $ fmap (fmap f) (tilesQd deps sC rC))
        ++ (cme $ fmap (fmap f) (tilesQd deps sD rD))
    =⟨ cong4 (λ l1 l2 l3 l4 -> l1 ++ l2 ++ l3 ++ l4) 
        (fmap-tilesQd f deps sA x1 y1 (min x2 (mid + x1)) (min y2 (mid + y1)) (min-rel-1 x1 mid x2 xp) (min-rel-1 y1 mid y2 yp) peqA peqB) 
        (fmap-tilesQd f deps sB (min x2 (mid + x1)) y1 x2 (min y2 (mid + y1)) (min-rel-2 x2 (mid + x1)) (min-rel-1 y1 mid y2 yp) peqA peqB) 
        (fmap-tilesQd f deps sC x1 (min y2 (mid + y1)) (min x2 (mid + x1)) y2 (min-rel-1 x1 mid x2 xp) (min-rel-2 y2 (mid + y1)) peqA peqB) 
        (fmap-tilesQd f deps sD (min x2 (mid + x1)) (min y2 (mid + y1)) x2 y2 (min-rel-2 x2 (mid + x1)) (min-rel-2 y2 (mid + y1)) peqA peqB) ⟩

        (cme $ (tilesQd deps (fmapₑ (quadrantFunctor deps) f sA) rA))
        ++ (cme $ (tilesQd deps (fmapₑ (quadrantFunctor deps) f sB) rB))
        ++ (cme $ (tilesQd deps (fmapₑ (quadrantFunctor deps) f sC) rC))
        ++ (cme $ (tilesQd deps (fmapₑ (quadrantFunctor deps) f sD) rD))
    =⟨ sym $ concat-cme4 (tilesQd deps (fmapₑ (quadrantFunctor deps) f sA) rA) (tilesQd deps (fmapₑ (quadrantFunctor deps) f sB) rB) (tilesQd deps (fmapₑ (quadrantFunctor deps) f sC) rC) _ ⟩
        (cme (
            tilesQd deps (fmapₑ (quadrantFunctor deps) f sA) rA
            ++ tilesQd deps (fmapₑ (quadrantFunctor deps) f sB) rB
            ++ tilesQd deps (fmapₑ (quadrantFunctor deps) f sC) rC
            ++ tilesQd deps (fmapₑ (quadrantFunctor deps) f sD) rD
        ))
    =⟨ tilesQd-concat deps (fmapₑ (quadrantFunctor deps) f sA) (fmapₑ (quadrantFunctor deps) f sB) (fmapₑ (quadrantFunctor deps) f sC) (fmapₑ (quadrantFunctor deps) f sD) x1 y1 x2 y2 xp yp peqB ⟩
        (cme $ tilesQd dep 
            (combine (fmapₑ (quadrantFunctor deps) f sA) (fmapₑ (quadrantFunctor deps) f sB) (fmapₑ (quadrantFunctor deps) f sC) (fmapₑ (quadrantFunctor deps) f sD)) reg)
    =⟨⟩
        (cme $ tilesQd dep (fmapₑ (quadrantFunctor dep) f vqd) reg)
    end where
        cme : List (Tile B) -> List B
        cme v = concat $ map expand $ v
        reg = (RegionC (x1 , y1) (x2 , y2))
        mid = pow 2 deps
        rA = (RegionC (x1 , y1) (min x2 (mid + x1) , min y2 (mid + y1)))
        rB = (RegionC (min x2 (mid + x1) , y1) (x2 , min y2 (mid + y1)))
        rC = (RegionC (x1 , min y2 (mid + y1)) (min x2 (mid + x1) , y2) )
        rD = (RegionC (min x2 (mid + x1) , min y2 (mid + y1)) (x2 , y2) )
        sA = CVQuadrant {dep = deps} a {aSub {dep = deps} a b c d p1}
        sB = CVQuadrant {dep = deps} b {bSub {dep = deps} a b c d p1}
        sC = CVQuadrant {dep = deps} c {cSub {dep = deps} a b c d p1}
        sD = CVQuadrant {dep = deps} d {dSub {dep = deps} a b c d p1}
fmap-tilesQd {A} {B} f dep@(S deps) vqd@(CVQuadrant (Node a@(Leaf _) b@(Node _ _ _ _) c d) {p1}) x1 y1 x2 y2 xp yp peqA peqB =
    begin
        (cme $ fmap (fmap f) $ tilesQd dep vqd reg)
    =⟨⟩
        (cme $ fmap (fmap f) $ (
            tilesQd deps sA rA ++ tilesQd deps sB rB ++ tilesQd deps sC rC ++ tilesQd deps sD rD
        ))
    =⟨ cong cme $ fmap-concat4 (fmap f) (tilesQd deps sA rA) (tilesQd deps sB rB) (tilesQd deps sC rC) (tilesQd deps sD rD) ⟩
        (cme (
            fmap (fmap f) (tilesQd deps sA rA) 
            ++ fmap (fmap f) (tilesQd deps sB rB)
            ++ fmap (fmap f) (tilesQd deps sC rC)
            ++ fmap (fmap f) (tilesQd deps sD rD)
        ))
    =⟨ concat-cme4 (fmap (fmap f) (tilesQd deps sA rA)) (fmap (fmap f) (tilesQd deps sB rB)) (fmap (fmap f) (tilesQd deps sC rC)) _ ⟩
        (cme $ fmap (fmap f) (tilesQd deps sA rA))
        ++ (cme $ fmap (fmap f) (tilesQd deps sB rB))
        ++ (cme $ fmap (fmap f) (tilesQd deps sC rC))
        ++ (cme $ fmap (fmap f) (tilesQd deps sD rD))
    =⟨ cong4 (λ l1 l2 l3 l4 -> l1 ++ l2 ++ l3 ++ l4) 
        (fmap-tilesQd f deps sA x1 y1 (min x2 (mid + x1)) (min y2 (mid + y1)) (min-rel-1 x1 mid x2 xp) (min-rel-1 y1 mid y2 yp) peqA peqB) 
        (fmap-tilesQd f deps sB (min x2 (mid + x1)) y1 x2 (min y2 (mid + y1)) (min-rel-2 x2 (mid + x1)) (min-rel-1 y1 mid y2 yp) peqA peqB) 
        (fmap-tilesQd f deps sC x1 (min y2 (mid + y1)) (min x2 (mid + x1)) y2 (min-rel-1 x1 mid x2 xp) (min-rel-2 y2 (mid + y1)) peqA peqB) 
        (fmap-tilesQd f deps sD (min x2 (mid + x1)) (min y2 (mid + y1)) x2 y2 (min-rel-2 x2 (mid + x1)) (min-rel-2 y2 (mid + y1)) peqA peqB) ⟩

        (cme $ (tilesQd deps (fmapₑ (quadrantFunctor deps) f sA) rA))
        ++ (cme $ (tilesQd deps (fmapₑ (quadrantFunctor deps) f sB) rB))
        ++ (cme $ (tilesQd deps (fmapₑ (quadrantFunctor deps) f sC) rC))
        ++ (cme $ (tilesQd deps (fmapₑ (quadrantFunctor deps) f sD) rD))
    =⟨ sym $ concat-cme4 (tilesQd deps (fmapₑ (quadrantFunctor deps) f sA) rA) (tilesQd deps (fmapₑ (quadrantFunctor deps) f sB) rB) (tilesQd deps (fmapₑ (quadrantFunctor deps) f sC) rC) _ ⟩
        (cme (
            tilesQd deps (fmapₑ (quadrantFunctor deps) f sA) rA
            ++ tilesQd deps (fmapₑ (quadrantFunctor deps) f sB) rB
            ++ tilesQd deps (fmapₑ (quadrantFunctor deps) f sC) rC
            ++ tilesQd deps (fmapₑ (quadrantFunctor deps) f sD) rD
        ))
    =⟨ tilesQd-concat deps (fmapₑ (quadrantFunctor deps) f sA) (fmapₑ (quadrantFunctor deps) f sB) (fmapₑ (quadrantFunctor deps) f sC) (fmapₑ (quadrantFunctor deps) f sD) x1 y1 x2 y2 xp yp peqB ⟩
        (cme $ tilesQd dep 
            (combine (fmapₑ (quadrantFunctor deps) f sA) (fmapₑ (quadrantFunctor deps) f sB) (fmapₑ (quadrantFunctor deps) f sC) (fmapₑ (quadrantFunctor deps) f sD)) reg)
    =⟨⟩
        (cme $ tilesQd dep (fmapₑ (quadrantFunctor dep) f vqd) reg)
    end where
        cme : List (Tile B) -> List B
        cme v = concat $ map expand $ v
        reg = (RegionC (x1 , y1) (x2 , y2))
        mid = pow 2 deps
        rA = (RegionC (x1 , y1) (min x2 (mid + x1) , min y2 (mid + y1)))
        rB = (RegionC (min x2 (mid + x1) , y1) (x2 , min y2 (mid + y1)))
        rC = (RegionC (x1 , min y2 (mid + y1)) (min x2 (mid + x1) , y2) )
        rD = (RegionC (min x2 (mid + x1) , min y2 (mid + y1)) (x2 , y2) )
        sA = CVQuadrant {dep = deps} a {aSub {dep = deps} a b c d p1}
        sB = CVQuadrant {dep = deps} b {bSub {dep = deps} a b c d p1}
        sC = CVQuadrant {dep = deps} c {cSub {dep = deps} a b c d p1}
        sD = CVQuadrant {dep = deps} d {dSub {dep = deps} a b c d p1}
fmap-tilesQd {A} {B} f dep@(S deps) vqd@(CVQuadrant (Node a@(Node _ _ _ _) b c d) {p1}) x1 y1 x2 y2 xp yp peqA peqB =
    begin
        (cme $ fmap (fmap f) $ tilesQd dep vqd reg)
    =⟨⟩
        (cme $ fmap (fmap f) $ (
            tilesQd deps sA rA ++ tilesQd deps sB rB ++ tilesQd deps sC rC ++ tilesQd deps sD rD
        ))
    =⟨ cong cme $ fmap-concat4 (fmap f) (tilesQd deps sA rA) (tilesQd deps sB rB) (tilesQd deps sC rC) (tilesQd deps sD rD) ⟩
        (cme (
            fmap (fmap f) (tilesQd deps sA rA) 
            ++ fmap (fmap f) (tilesQd deps sB rB)
            ++ fmap (fmap f) (tilesQd deps sC rC)
            ++ fmap (fmap f) (tilesQd deps sD rD)
        ))
    =⟨ concat-cme4 (fmap (fmap f) (tilesQd deps sA rA)) (fmap (fmap f) (tilesQd deps sB rB)) (fmap (fmap f) (tilesQd deps sC rC)) _ ⟩
        (cme $ fmap (fmap f) (tilesQd deps sA rA))
        ++ (cme $ fmap (fmap f) (tilesQd deps sB rB))
        ++ (cme $ fmap (fmap f) (tilesQd deps sC rC))
        ++ (cme $ fmap (fmap f) (tilesQd deps sD rD))
    =⟨ cong4 (λ l1 l2 l3 l4 -> l1 ++ l2 ++ l3 ++ l4) 
        (fmap-tilesQd f deps sA x1 y1 (min x2 (mid + x1)) (min y2 (mid + y1)) (min-rel-1 x1 mid x2 xp) (min-rel-1 y1 mid y2 yp) peqA peqB) 
        (fmap-tilesQd f deps sB (min x2 (mid + x1)) y1 x2 (min y2 (mid + y1)) (min-rel-2 x2 (mid + x1)) (min-rel-1 y1 mid y2 yp) peqA peqB) 
        (fmap-tilesQd f deps sC x1 (min y2 (mid + y1)) (min x2 (mid + x1)) y2 (min-rel-1 x1 mid x2 xp) (min-rel-2 y2 (mid + y1)) peqA peqB) 
        (fmap-tilesQd f deps sD (min x2 (mid + x1)) (min y2 (mid + y1)) x2 y2 (min-rel-2 x2 (mid + x1)) (min-rel-2 y2 (mid + y1)) peqA peqB) ⟩

        (cme $ (tilesQd deps (fmapₑ (quadrantFunctor deps) f sA) rA))
        ++ (cme $ (tilesQd deps (fmapₑ (quadrantFunctor deps) f sB) rB))
        ++ (cme $ (tilesQd deps (fmapₑ (quadrantFunctor deps) f sC) rC))
        ++ (cme $ (tilesQd deps (fmapₑ (quadrantFunctor deps) f sD) rD))
    =⟨ sym $ concat-cme4 (tilesQd deps (fmapₑ (quadrantFunctor deps) f sA) rA) (tilesQd deps (fmapₑ (quadrantFunctor deps) f sB) rB) (tilesQd deps (fmapₑ (quadrantFunctor deps) f sC) rC) _ ⟩
        (cme (
            tilesQd deps (fmapₑ (quadrantFunctor deps) f sA) rA
            ++ tilesQd deps (fmapₑ (quadrantFunctor deps) f sB) rB
            ++ tilesQd deps (fmapₑ (quadrantFunctor deps) f sC) rC
            ++ tilesQd deps (fmapₑ (quadrantFunctor deps) f sD) rD
        ))
    =⟨ tilesQd-concat deps (fmapₑ (quadrantFunctor deps) f sA) (fmapₑ (quadrantFunctor deps) f sB) (fmapₑ (quadrantFunctor deps) f sC) (fmapₑ (quadrantFunctor deps) f sD) x1 y1 x2 y2 xp yp peqB ⟩
        (cme $ tilesQd dep 
            (combine (fmapₑ (quadrantFunctor deps) f sA) (fmapₑ (quadrantFunctor deps) f sB) (fmapₑ (quadrantFunctor deps) f sC) (fmapₑ (quadrantFunctor deps) f sD)) reg)
    =⟨⟩
        (cme $ tilesQd dep (fmapₑ (quadrantFunctor dep) f vqd) reg)
    end where
        cme : List (Tile B) -> List B
        cme v = concat $ map expand $ v
        reg = (RegionC (x1 , y1) (x2 , y2))
        mid = pow 2 deps
        rA = (RegionC (x1 , y1) (min x2 (mid + x1) , min y2 (mid + y1)))
        rB = (RegionC (min x2 (mid + x1) , y1) (x2 , min y2 (mid + y1)))
        rC = (RegionC (x1 , min y2 (mid + y1)) (min x2 (mid + x1) , y2) )
        rD = (RegionC (min x2 (mid + x1) , min y2 (mid + y1)) (x2 , y2) )
        sA = CVQuadrant {dep = deps} a {aSub {dep = deps} a b c d p1}
        sB = CVQuadrant {dep = deps} b {bSub {dep = deps} a b c d p1}
        sC = CVQuadrant {dep = deps} c {cSub {dep = deps} a b c d p1}
        sD = CVQuadrant {dep = deps} d {dSub {dep = deps} a b c d p1}

qdToQt : {A : Set} {{eqA : Eq A}} -> (dep w h : Nat) -> (vqd : VQuadrant A {dep}) -> .(q : IsTrue (dep == log2up (if w < h then h else w)))
    -> tilesQd dep vqd (RegionC (0 , 0) (w , h)) ≡ tilesQt dep (toQt dep w h q vqd)
qdToQt dep w h (CVQuadrant qd {p}) q = refl

fmap-tilesQt : {A B : Set} {{eqA : Eq A}} {{eqB : Eq B}} -> (f : A -> B) -> (dep : Nat) -> (vqt : VQuadTree A {dep})
    -> ({a b : A} -> IsTrue (a == b) -> a ≡ b)
    -> ({a b : B} -> IsTrue (a == b) -> a ≡ b)
    -> (concat $ map expand $ fmap (fmap f) $ tilesQt dep vqt) ≡ (concat $ map expand $ tilesQt dep $ fmapₑ (quadtreeFunctor dep) f vqt)
fmap-tilesQt f dep (CVQuadTree (Wrapper (w , h) (Leaf v))) peqA peqB = refl
fmap-tilesQt {A} {B} f dep@(S deps) vqt@(CVQuadTree (Wrapper (w , h) qd@(Node a b c d)) {p1} {p2}) peqA peqB =
    begin
        (concat $ map expand $ fmap (fmap f) $ tilesQt dep vqt)
    =⟨⟩
        (concat $ map expand $ fmap (fmap f) $ tilesQd dep (CVQuadrant qd {p1}) (RegionC (0 , 0) (w , h)))
    =⟨ fmap-tilesQd f dep (CVQuadrant qd {p1}) 0 0 w h (zeroLteAny w) (zeroLteAny h) peqA peqB ⟩
        (concat $ map expand $ tilesQd dep (fmapₑ (quadrantFunctor dep) f (CVQuadrant qd {p1})) (RegionC (0 , 0) (w , h)))
    =⟨ cong (λ l -> concat $ map expand l) (qdToQt dep w h (combine (fmapₑ (quadrantFunctor deps) f (CVQuadrant a)) _ _ _) p2) ⟩
        (concat $ map expand $ tilesQt dep (fmapₑ (quadtreeFunctor dep) f vqt))
    end

proof-foldfmap-qt : {t s : Set} {{eqT : Eq t}} {{eqS : Eq s}} {{monS : Monoid s}} {{monT : Monoid t}} (dep : Nat) -> (vqt : VQuadTree t {dep})
    -> (f : t -> s)
    -> ({a b : t} -> IsTrue (a == b) -> a ≡ b)
    -> ({a b : s} -> IsTrue (a == b) -> a ≡ b)
    -> foldMapₑ (quadtreeFoldable dep) f vqt ≡ foldMapₑ (quadtreeFoldable dep) id (fmapₑ (quadtreeFunctor dep) f vqt)
proof-foldfmap-qt {t} {s} dep vqt@(CVQuadTree (Wrapper (w , h) (Leaf v)) {p} {q}) f peqA peqB = 
    begin
        foldMapₑ (quadtreeFoldable dep) f vqt
    =⟨⟩
        foldMap f (replicateₙ (w * h) v ++ [])
    =⟨ cong (foldMap f) (concat-nothing (replicateₙ (w * h) v)) ⟩
        foldMap f (replicateₙ (w * h) v)
    =⟨ proof-foldfmap-list (replicateₙ (w * h) v) f ⟩
        foldMap id (fmap f (replicateₙ (w * h) v))
    =⟨ cong (foldMap id) (fmap-replicate f v (w * h)) ⟩
        foldMap id (replicateₙ (w * h) (f v))
    =⟨ cong (foldMap id) (sym $ concat-nothing (replicateₙ (w * h) (f v))) ⟩
        foldMap id (replicateₙ (w * h) (f v) ++ [])
    =⟨⟩
        foldMapₑ (quadtreeFoldable dep) id (fmapₑ (quadtreeFunctor dep) f vqt)
    end
proof-foldfmap-qt {t} {s} dep vqt@(CVQuadTree (Wrapper (w , h) (Node qd qd₁ qd₂ qd₃)) {p} {q}) f peqA peqB =
    begin
        foldMapₑ (quadtreeFoldable dep) f vqt
    =⟨⟩
        (foldMap f $ concat $ map expand $ tilesQt dep vqt)
    =⟨ proof-foldfmap-list (concat $ map expand $ tilesQt dep vqt) f ⟩
        (foldMap id $ fmap f $ concat $ map expand $ tilesQt dep vqt)
    =⟨ cong (foldMap id) (fmap-concat-expand f (tilesQt dep vqt)) ⟩
        (foldMap id $ concat $ map expand $ fmap (fmap f) $ tilesQt dep vqt)
    =⟨ cong (foldMap id) (fmap-tilesQt f dep vqt peqA peqB) ⟩
        (foldMap id $ concat $ map expand $ tilesQt dep $ fmapₑ (quadtreeFunctor dep) f vqt)
    =⟨⟩ 
        foldMapₑ (quadtreeFoldable dep) id (fmapₑ (quadtreeFunctor dep) f vqt)
    end