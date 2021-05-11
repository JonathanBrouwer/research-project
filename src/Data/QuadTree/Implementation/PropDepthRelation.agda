module Data.QuadTree.Implementation.PropDepthRelation where

open import Haskell.Prelude
open import Data.Logic

---- Properties of depth

lteTransitiveWeird : (x y d : Nat) -> IsTrue (x < y) -> (y <= d) ≡ ((x <= d) && (y <= d))
lteTransitiveWeird zero zero zero xlty = refl
lteTransitiveWeird zero zero (suc d) xlty = refl
lteTransitiveWeird zero (suc y) zero xlty = refl
lteTransitiveWeird zero (suc y) (suc d) xlty = refl
lteTransitiveWeird (suc x) (suc y) zero xlty = refl
lteTransitiveWeird (suc x) (suc y) (suc d) xlty = lteTransitiveWeird x y d xlty

lteTransitiveWeirdInv : (x y d : Nat) -> IsFalse (x < y) -> (x <= d) ≡ ((x <= d) && (y <= d))
lteTransitiveWeirdInv zero zero zero xnlty = refl
lteTransitiveWeirdInv zero zero (suc d) xnlty = refl
lteTransitiveWeirdInv (suc x) zero zero xnlty = refl
lteTransitiveWeirdInv (suc x) zero (suc d) xnlty =
  begin
    (suc x <= suc d)
  =⟨ sym $ boolAndTrue (suc x <= suc d) ⟩
    (suc x <= suc d) && true
  =⟨⟩
    ((suc x <= suc d) && (zero <= suc d))
  end
lteTransitiveWeirdInv (suc x) (suc y) zero xnlty = refl
lteTransitiveWeirdInv (suc x) (suc y) (suc d) xnlty = lteTransitiveWeirdInv x y d xnlty

ifComparisonMap : (x y d : Nat) -> ((x <= d) && (y <= d)) ≡ (if x < y then (y <= d) else (x <= d))
ifComparisonMap x y d = ifc x < y 
  then (λ {{xlty}} ->
    begin
      (x <= d) && (y <= d)
    =⟨ sym $ lteTransitiveWeird x y d xlty ⟩
      y <= d
    =⟨ sym $ ifTrue (x < y) xlty ⟩
      (if x < y then (y <= d) else (x <= d))
    end
  )
  else (λ {{xnlty}} ->
    begin
      (x <= d) && (y <= d)
    =⟨ sym $ lteTransitiveWeirdInv x y d xnlty ⟩
      x <= d
    =⟨ sym $ ifFalse (x < y) xnlty ⟩
      (if x < y then (y <= d) else (x <= d))
    end
  )

propMaxLte : (x y d : Nat) -> ((x <= d) && (y <= d)) ≡ (max x y <= d)
propMaxLte x y d = 
  begin
    (x <= d) && (y <= d)
  =⟨ ifComparisonMap x y d ⟩
    (if x < y then (y <= d) else (x <= d))
  =⟨ propFnIf (λ v -> v <= d) ⟩
    (if x < y then y else x) <= d
  =⟨⟩
    max x y <= d
  end

propAndMap : (a b c d : Bool) -> a ≡ c -> b ≡ d -> (a && b) ≡ (c && d)
propAndMap false false false false ac bd = refl
propAndMap false true false true ac bd = refl
propAndMap true false true false ac bd = refl
propAndMap true true true true ac bd = refl

propMaxLte4 : (w x y z d : Nat) -> (((w <= d) && (x <= d)) && ((y <= d) && (z <= d))) ≡ (max (max w x) (max y z) <= d)
propMaxLte4 w x y z d =
  begin
    ((w <= d) && (x <= d)) && ((y <= d) && (z <= d))
  =⟨ propAndMap ((w <= d) && (x <= d)) ((y <= d) && (z <= d)) (max w x <= d) (max y z <= d) (propMaxLte w x d) (propMaxLte y z d) ⟩
    (max w x <= d) && (max y z <= d)
  =⟨ propMaxLte (if w < x then x else w) (if y < z then z else y) d ⟩
    (max (max w x) (max y z) <= d)
  end
