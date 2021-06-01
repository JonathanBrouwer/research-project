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

concat-nothing : {A : Set} -> (l : List A) -> l ++ [] ≡ l
concat-nothing [] = refl
concat-nothing (x ∷ xs) = cong (λ z → x ∷ z) (concat-nothing xs)

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


tileQd-combine : {A : Set} {{eqA : Eq A}} -> (deps x1 y1 x2 y2 : Nat) -> (qA qB qC qD : VQuadrant A {deps})
    -> tilesQd (S deps) (combine qA qB qC qD) (RegionC (x1 , y1) (x2 , y2))
         ≡ (tilesQd deps qA (RegionC (x1 , y1) (min x2 (pow 2 deps + x1) , min y2 (pow 2 deps + y1)))) 
        ++ (tilesQd deps qB (RegionC (min x2 (pow 2 deps + x1) , y1) (x2 , min y2 (pow 2 deps + y1)))) 
        ++ (tilesQd deps qC (RegionC (x1 , min y2 (pow 2 deps + y1)) (min x2 (pow 2 deps + x1) , y2) )) 
        ++ (tilesQd deps qD (RegionC (min x2 (pow 2 deps + x1) , min y2 (pow 2 deps + y1)) (x2 , y2) ))
tileQd-combine deps x1 y1 x2 y2 qA@(CVQuadrant qa@(Leaf va)) qB@(CVQuadrant qb@(Leaf vb)) qC@(CVQuadrant qc@(Leaf vc)) qD@(CVQuadrant qd@(Leaf vd)) =
    ifc (va == vb) && (vb == vc) && (vc == vd)
    then (λ {{p}} -> 
        begin
            tilesQd (S deps)
                (ifc (va == vb) && (vb == vc) && (vc == vd)
                    then CVQuadrant (Leaf va) 
                    else CVQuadrant (Node (Leaf va) (Leaf vb) (Leaf vc) (Leaf vd)))
                (RegionC (x1 , y1) (x2 , y2))
        =⟨ cong (λ x -> tilesQd (S deps) x (RegionC (x1 , y1) (x2 , y2))) (ifcTrue ((va == vb) && (vb == vc) && (vc == vd)) p) ⟩
            tilesQd (S deps)
                (CVQuadrant (Leaf va) {IsTrue.itsTrue})
                (RegionC (x1 , y1) (x2 , y2))
        =⟨ {!   !} ⟩
            {!   !}
        end)
    else (λ {{p}} -> {!   !})
tileQd-combine deps x1 y1 x2 y2 (CVQuadrant qa@(Leaf a)) (CVQuadrant qb@(Leaf b)) (CVQuadrant qc@(Leaf c)) (CVQuadrant qd@(Node d1 d2 d3 d4)) = {! refl  !}
tileQd-combine deps x1 y1 x2 y2 (CVQuadrant qa@(Leaf a)) (CVQuadrant qb@(Leaf b)) (CVQuadrant qc@(Node c1 c2 c3 c4)) (CVQuadrant qd) = {!   !}
tileQd-combine deps x1 y1 x2 y2 (CVQuadrant qa@(Leaf a)) (CVQuadrant qb@(Node b1 b2 b3 b4)) (CVQuadrant qc) (CVQuadrant qd) = {!   !}
tileQd-combine deps x1 y1 x2 y2 (CVQuadrant qa@(Node a1 a2 a3 a4)) (CVQuadrant qb) (CVQuadrant qc) (CVQuadrant qd) = {! refl  !}

fmap-tilesQd : {A B : Set} {{eqA : Eq A}} {{eqB : Eq B}} -> (f : A -> B) -> (dep : Nat) -> (vqd : VQuadrant A {dep}) -> (reg : Region)
    -> (fmap (fmap f) $ tilesQd dep vqd reg) ≡ (tilesQd dep (fmapₑ (quadrantFunctor dep) f vqd) reg)
fmap-tilesQd f dep (CVQuadrant (Leaf v)) (RegionC (x1 , y1) (x2 , y2)) = refl
fmap-tilesQd {t} f dep@(S deps) vqd@(CVQuadrant qd@(Node a b c d) {p1}) reg@(RegionC (x1 , y1) (x2 , y2)) =
    begin
        (fmap (fmap f) $ 
        (tilesQd deps qA rA
        ++ tilesQd deps qB rB 
        ++ tilesQd deps qC rC 
        ++ tilesQd deps qD rD))
    =⟨ fmap-concat4 (fmap f) (tilesQd deps qA rA) (tilesQd deps qB rB) (tilesQd deps qC rC) _ ⟩
        (fmap (fmap f) (tilesQd deps qA rA)) 
        ++ (fmap (fmap f) (tilesQd deps qB rB)) 
        ++ (fmap (fmap f) (tilesQd deps qC rC)) 
        ++ (fmap (fmap f) (tilesQd deps qD rD))
    =⟨ cong4 (λ l1 l2 l3 l4 -> l1 ++ l2 ++ l3 ++ l4) (fmap-tilesQd f deps qA rA) (fmap-tilesQd f deps qB rB) (fmap-tilesQd f deps qC rC) (fmap-tilesQd f deps qD rD) ⟩
        (tilesQd deps (fmapₑ (quadrantFunctor deps) f qA) rA) 
        ++ (tilesQd deps (fmapₑ (quadrantFunctor deps) f qB) rB) 
        ++ (tilesQd deps (fmapₑ (quadrantFunctor deps) f qC) rC) 
        ++ (tilesQd deps (fmapₑ (quadrantFunctor deps) f qD) rD)
    =⟨ sym $ tileQd-combine deps x1 y1 x2 y2 (fmapₑ (quadrantFunctor deps) f qA) (fmapₑ (quadrantFunctor deps) f qB) (fmapₑ (quadrantFunctor deps) f qC) (fmapₑ (quadrantFunctor deps) f qD) ⟩
        (tilesQd dep (fmapₑ (quadrantFunctor dep) f vqd) reg)
    end where
        mid = pow 2 deps
        qA = (CVQuadrant a {aSub a b c d p1})
        rA = (RegionC (x1 , y1) (min x2 (mid + x1) , min y2 (mid + y1)))
        qB = (CVQuadrant b {bSub a b c d p1})
        rB = (RegionC (min x2 (mid + x1) , y1) (x2 , min y2 (mid + y1)))
        qC = (CVQuadrant c {cSub a b c d p1})
        rC = (RegionC (x1 , min y2 (mid + y1)) (min x2 (mid + x1) , y2) )
        qD = (CVQuadrant d {dSub a b c d p1})
        rD = (RegionC (min x2 (mid + x1) , min y2 (mid + y1)) (x2 , y2) )


qdToQt : {A : Set} {{eqA : Eq A}} -> (dep w h : Nat) -> (vqd : VQuadrant A {dep}) -> .(q : IsTrue (dep == log2up (if w < h then h else w)))
    -> tilesQd dep vqd (RegionC (0 , 0) (w , h)) ≡ tilesQt dep (toQt dep w h q vqd)
qdToQt dep w h (CVQuadrant qd {p}) q = refl

fmap-tilesQt : {A B : Set} {{eqA : Eq A}} {{eqB : Eq B}} -> (f : A -> B) -> (dep : Nat) -> (vqt : VQuadTree A {dep})
    -> (fmap (fmap f) $ tilesQt dep vqt) ≡ (tilesQt dep $ fmapₑ (quadtreeFunctor dep) f vqt)
fmap-tilesQt {A} {B} f dep vqt@(CVQuadTree (Wrapper (w , h) qd@(Leaf x)) {p1} {p2}) = refl
fmap-tilesQt {A} {B} f dep@(S deps) vqt@(CVQuadTree (Wrapper (w , h) qd@(Node a b c d)) {p1} {p2}) =
    begin
        (fmap (fmap f) $ tilesQt dep vqt)
    =⟨⟩
        (fmap (fmap f) $ tilesQd dep (CVQuadrant qd {p1}) (RegionC (0 , 0) (w , h)))
    =⟨ fmap-tilesQd f dep (CVQuadrant qd {p1}) (RegionC (0 , 0) (w , h)) ⟩
        (tilesQd dep (fmapₑ (quadrantFunctor dep) f (CVQuadrant qd {p1})) (RegionC (0 , 0) (w , h)))
    =⟨ qdToQt dep w h (combine (fmapₑ (quadrantFunctor deps) f (CVQuadrant a)) _ _ _) p2 ⟩
        (tilesQt dep (fmapₑ (quadtreeFunctor dep) f vqt))
    end where


proof-foldfmap-qt : {t s : Set} {{eqT : Eq t}} {{eqS : Eq s}} {{monS : Monoid s}} {{monT : Monoid t}} (dep : Nat) -> (vqt : VQuadTree t {dep})
    -> (f : t -> s)
    -> foldMapₑ (quadtreeFoldable dep) f vqt ≡ foldMapₑ (quadtreeFoldable dep) id (fmapₑ (quadtreeFunctor dep) f vqt)
proof-foldfmap-qt {t} {s} dep vqt@(CVQuadTree (Wrapper (w , h) (Leaf v)) {p} {q}) f = 
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
proof-foldfmap-qt {t} {s} dep vqt@(CVQuadTree (Wrapper (w , h) (Node qd qd₁ qd₂ qd₃)) {p} {q}) f =
    begin
        foldMapₑ (quadtreeFoldable dep) f vqt
    =⟨⟩
        (foldMap f $ concat $ map expand $ tilesQt dep vqt)
    =⟨ proof-foldfmap-list (concat $ map expand $ tilesQt dep vqt) f ⟩
        (foldMap id $ fmap f $ concat $ map expand $ tilesQt dep vqt)
    =⟨ cong (foldMap id) (fmap-concat-expand f (tilesQt dep vqt)) ⟩
        (foldMap id $ concat $ map expand $ fmap (fmap f) $ tilesQt dep vqt)
    =⟨ cong (λ q -> foldMap id $ concat $ map expand q) (fmap-tilesQt f dep vqt) ⟩
        (foldMap id $ concat $ map expand $ tilesQt dep $ fmapₑ (quadtreeFunctor dep) f vqt)
    =⟨⟩ 
        foldMapₑ (quadtreeFoldable dep) id (fmapₑ (quadtreeFunctor dep) f vqt)
    end