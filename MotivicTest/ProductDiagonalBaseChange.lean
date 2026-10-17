/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProductDiagonalBaseChange

/-!
# Consumers of base-changed product diagonals

The literal parameter quotient and Cartesian squares work without reducedness,
separatedness, smoothness, or any flatness assumption. Flatness is required
only for the flatness conclusions, on precisely the two indicated maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProductDiagonal AlgebraicGeometry.ProductDiagonalBaseChange

universe u

namespace MotivicTest.ProductDiagonalBaseChange

variable {S Y T P D : Scheme.{u}} (y : Y ⟶ S) (t : T ⟶ S)
  (q : P ⟶ ambient y t)

example [Flat y] : Flat (parameterPair y t) := inferInstance

example [Flat y] [Flat q] : Flat (q ≫ parameterPair y t) := inferInstance

example [IsSeparated t] : IsClosedImmersion (quotientInclusion y t q) := inferInstance

example : parameterQuotient y t q =
    pullback (pullback.diagonal t) (q ≫ parameterPair y t) := rfl

example : IsPullback (quotientMap y t q) (quotientInclusion y t q) (inclusion y t) q :=
  quotientMap_isPullback y t q

example [Flat q] : Flat (quotientMap y t q) := inferInstance

example [Flat t] [Flat q] : Flat (remainingMap y t q) := inferInstance

example : remainingMap y t q ≫ pullback.fst y y = quotientInclusion y t q ≫ q ≫
    pullback.fst (productBase y t) (productBase y t) ≫ pullback.fst y t :=
  remainingMap_fst y t q

example : remainingMap y t q ≫ pullback.snd y y = quotientInclusion y t q ≫ q ≫
    pullback.snd (productBase y t) (productBase y t) ≫ pullback.fst y t :=
  remainingMap_snd y t q

variable (a : D ⟶ product y t) (i : D ⟶ P)
  (sq : IsPullback a i (pullback.diagonal (productBase y t)) q)

example : diagonalLift y t q a i sq ≫ quotientInclusion y t q = i :=
  diagonalLift_quotientInclusion y t q a i sq

example : diagonalLift y t q a i sq ≫
    pullback.fst (pullback.diagonal t) (q ≫ parameterPair y t) = a ≫ pullback.snd y t :=
  diagonalLift_parameter y t q a i sq

example : IsPullback (a ≫ pullback.fst y t) (diagonalLift y t q a i sq)
    (pullback.diagonal y) (remainingMap y t q) := diagonalLift_isPullback y t q a i sq

example : D ≅ pullback (pullback.diagonal y) (remainingMap y t q) :=
  (diagonalLift_isPullback y t q a i sq).isoPullback

end MotivicTest.ProductDiagonalBaseChange
