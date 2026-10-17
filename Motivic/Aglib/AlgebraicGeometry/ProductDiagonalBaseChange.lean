/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProductDiagonal
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Base change of the product-diagonal decomposition

For an arbitrary map to a pair of parameterized points, the literal inverse
image of the parameter diagonal maps to the universal parameter-diagonal
scheme by base change. If the arbitrary map and the parameter morphism are
flat, its remaining pair of original coordinates is flat. The inverse image
of the full product diagonal is the Cartesian inverse image of the original
diagonal along this remaining pair. All constructions use the full schemes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProductDiagonal

universe u

namespace AlgebraicGeometry.ProductDiagonalBaseChange

variable {S Y T P : Scheme.{u}} (y : Y ⟶ S) (t : T ⟶ S)
  (q : P ⟶ ambient y t)

/-- The universal parameter-pair map is flat when the original scheme is flat
    over the base. -/
instance parameterPair_flat [Flat y] : Flat (parameterPair y t) := by
  unfold parameterPair
  exact MorphismProperty.pullbackMap (P := @Flat)
    (inferInstance : Flat (pullback.snd y t))
    (inferInstance : Flat (pullback.snd y t)) pullback.condition pullback.condition

/-- The literal inverse image of the parameter diagonal along the given map. -/
abbrev parameterQuotient := pullback (pullback.diagonal t) (q ≫ parameterPair y t)

/-- The actual projection from the parameter-diagonal inverse image. -/
abbrev quotientInclusion : parameterQuotient y t q ⟶ P :=
  pullback.snd (pullback.diagonal t) (q ≫ parameterPair y t)

instance quotientInclusion_isClosedImmersion [IsSeparated t] :
    IsClosedImmersion (quotientInclusion y t q) := inferInstance

/-- The map to the universal parameter-diagonal scheme. -/
def quotientMap : parameterQuotient y t q ⟶ parameterDiagonal y t :=
  pullback.lift
    (pullback.fst (pullback.diagonal t) (q ≫ parameterPair y t))
    (quotientInclusion y t q ≫ q)
    (by simpa only [Category.assoc] using
      (pullback.condition (f := pullback.diagonal t) (g := q ≫ parameterPair y t)))

@[reassoc (attr := simp)]
theorem quotientMap_parameter :
    quotientMap y t q ≫ pullback.fst (pullback.diagonal t) (parameterPair y t) =
      pullback.fst (pullback.diagonal t) (q ≫ parameterPair y t) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem quotientMap_inclusion :
    quotientMap y t q ≫ inclusion y t = quotientInclusion y t q ≫ q :=
  pullback.lift_snd _ _ _

/-- The quotient map is the actual base change of the given ambient map. -/
theorem quotientMap_isPullback :
    IsPullback (quotientMap y t q) (quotientInclusion y t q) (inclusion y t) q := by
  apply IsPullback.of_right
    (h₁₂ := pullback.fst (pullback.diagonal t) (parameterPair y t))
    (h₂₂ := parameterPair y t)
  · simpa only [quotientMap_parameter] using
      (IsPullback.of_hasPullback (pullback.diagonal t) (q ≫ parameterPair y t))
  · exact quotientMap_inclusion y t q
  · exact IsPullback.of_hasPullback _ _

instance quotientMap_flat [Flat q] : Flat (quotientMap y t q) :=
  MorphismProperty.of_isPullback (quotientMap_isPullback y t q).flip inferInstance

/-- The remaining pair of original coordinates on the actual inverse image. -/
def remainingMap : parameterQuotient y t q ⟶ pullback y y :=
  quotientMap y t q ≫ remainingYPair y t

instance remainingMap_flat [Flat t] [Flat q] : Flat (remainingMap y t q) := by
  unfold remainingMap
  infer_instance

@[reassoc]
theorem remainingMap_fst :
    remainingMap y t q ≫ pullback.fst y y = quotientInclusion y t q ≫ q ≫
      pullback.fst (productBase y t) (productBase y t) ≫ pullback.fst y t := by
  simp only [remainingMap, Category.assoc, remainingYPair_fst,
    quotientMap_inclusion_assoc]

@[reassoc]
theorem remainingMap_snd :
    remainingMap y t q ≫ pullback.snd y y = quotientInclusion y t q ≫ q ≫
      pullback.snd (productBase y t) (productBase y t) ≫ pullback.fst y t := by
  simp only [remainingMap, Category.assoc, remainingYPair_snd,
    quotientMap_inclusion_assoc]

variable {D : Scheme.{u}} (a : D ⟶ product y t) (i : D ⟶ P)
  (sq : IsPullback a i (pullback.diagonal (productBase y t)) q)

/-- The full-diagonal inverse image lifted through the parameter quotient. -/
def diagonalLift : D ⟶ parameterQuotient y t q :=
  (quotientMap_isPullback y t q).lift (a ≫ fullDiagonalLift y t) i
    (by simpa only [Category.assoc, fullDiagonalLift_inclusion] using sq.w)

@[reassoc (attr := simp)]
theorem diagonalLift_quotientInclusion :
    diagonalLift y t q a i sq ≫ quotientInclusion y t q = i :=
  IsPullback.lift_snd _ _ _ _

@[reassoc (attr := simp)]
theorem diagonalLift_quotientMap :
    diagonalLift y t q a i sq ≫ quotientMap y t q = a ≫ fullDiagonalLift y t :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
theorem diagonalLift_parameter :
    diagonalLift y t q a i sq ≫
      pullback.fst (pullback.diagonal t) (q ≫ parameterPair y t) = a ≫ pullback.snd y t := by
  rw [← quotientMap_parameter y t q, ← Category.assoc, diagonalLift_quotientMap]
  simp only [Category.assoc, fullDiagonalLift_parameter]

/-- Removing only the parameter diagonal from the original Cartesian square. -/
theorem diagonalLift_quotientMap_isPullback :
    IsPullback a (diagonalLift y t q a i sq) (fullDiagonalLift y t) (quotientMap y t q) := by
  apply IsPullback.of_bot (v₂₁ := quotientInclusion y t q) (v₂₂ := inclusion y t)
  · simpa only [diagonalLift_quotientInclusion, fullDiagonalLift_inclusion] using sq
  · exact (diagonalLift_quotientMap y t q a i sq).symm
  · exact quotientMap_isPullback y t q

/-- The full-diagonal inverse image is exactly the remaining original-diagonal
base change after imposing the parameter diagonal. -/
theorem diagonalLift_isPullback :
    IsPullback (a ≫ pullback.fst y t) (diagonalLift y t q a i sq)
      (pullback.diagonal y) (remainingMap y t q) :=
  (diagonalLift_quotientMap_isPullback y t q a i sq).paste_horiz
    (fullDiagonalLift_isPullback y t)

end AlgebraicGeometry.ProductDiagonalBaseChange
