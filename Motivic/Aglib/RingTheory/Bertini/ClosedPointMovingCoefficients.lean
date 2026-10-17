/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Actual coefficient algebras at the original closed point

For a closed point `p` of a finite-type `k`-algebra `R`, the coefficient algebra
is literally `R ⊗[k] κ(p)`, with the moving copy of `R` on the left. Its finiteness
over `R` follows from Zariski's lemma, not from an assumed rational point or a
supplied finite-dimensional extension. No domain assumption on this tensor
product is made.

The canonical diagonal evaluation identifies the moving and selected values of
each original generator. Its kernel contracts to exactly the original point.
-/
@[expose] public noncomputable section

open scoped TensorProduct

namespace QuadraticIncidence.ClosedPoint

universe u v
variable (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
  (p : PrimeSpectrum R)

/-- The actual moving-point coefficient algebra, with the original ring on the left. -/
abbrev CoefficientRing := R ⊗[k] p.asIdeal.ResidueField

/-- A closed point of a finite-type algebra has a finite residue extension. -/
theorem residueField_finite [Algebra.FiniteType k R] [p.asIdeal.IsMaximal] :
    Module.Finite k p.asIdeal.ResidueField := by
  let : Algebra.FiniteType k p.asIdeal.ResidueField :=
    Algebra.FiniteType.of_surjective
      (IsScalarTower.toAlgHom k R p.asIdeal.ResidueField)
      p.asIdeal.algebraMap_residueField_surjective
  exact finite_of_finite_type_of_isJacobsonRing k p.asIdeal.ResidueField

/-- Finiteness of the actual coefficient algebra is derived from closedness. -/
instance coefficientRing_finite [Algebra.FiniteType k R] [p.asIdeal.IsMaximal] :
    Module.Finite R (CoefficientRing k R p) := by
  let := residueField_finite k R p
  exact Module.Finite.base_change k R p.asIdeal.ResidueField

/-- The selected value is the unchanged residue of the original element. -/
def selectedValue (r : R) : CoefficientRing k R p :=
  1 ⊗ₜ[k] algebraMap R p.asIdeal.ResidueField r

/-- The moving value is the original element in the left tensor factor. -/
def movingValue (r : R) : CoefficientRing k R p :=
  algebraMap R (CoefficientRing k R p) r

/-- The literal difference between the original moving and selected values. -/
def difference (r : R) : CoefficientRing k R p :=
  movingValue k R p r - selectedValue k R p r

theorem difference_eq (r : R) :
    difference k R p r = algebraMap R (CoefficientRing k R p) r -
      1 ⊗ₜ[k] algebraMap R p.asIdeal.ResidueField r := rfl

/-- Evaluation on the original diagonal, `r ⊗ l ↦ residue(r) * l`. -/
def diagonalEvaluation : CoefficientRing k R p →ₐ[k] p.asIdeal.ResidueField :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom k R p.asIdeal.ResidueField)
    (AlgHom.id k p.asIdeal.ResidueField) (fun _ _ ↦ Commute.all _ _)

@[simp]
theorem diagonalEvaluation_tmul (r : R) (l : p.asIdeal.ResidueField) :
    diagonalEvaluation k R p (r ⊗ₜ[k] l) =
      algebraMap R p.asIdeal.ResidueField r * l := rfl

@[simp]
theorem diagonalEvaluation_selectedValue (r : R) :
    diagonalEvaluation k R p (selectedValue k R p r) =
      algebraMap R p.asIdeal.ResidueField r := by
  simp [selectedValue]

@[simp]
theorem diagonalEvaluation_movingValue (r : R) :
    diagonalEvaluation k R p (movingValue k R p r) =
      algebraMap R p.asIdeal.ResidueField r := by
  simp [movingValue, Algebra.TensorProduct.algebraMap_apply]

@[simp]
theorem diagonalEvaluation_difference (r : R) :
    diagonalEvaluation k R p (difference k R p r) = 0 := by
  simp [difference]

/-- Every original coordinate difference belongs to the actual diagonal kernel. -/
theorem difference_mem_diagonalKernel (r : R) :
    difference k R p r ∈ RingHom.ker (diagonalEvaluation k R p).toRingHom :=
  diagonalEvaluation_difference k R p r

/-- The diagonal evaluation has the entire residue field as its image. -/
theorem diagonalEvaluation_surjective : Function.Surjective (diagonalEvaluation k R p) := by
  intro l
  refine ⟨1 ⊗ₜ[k] l, ?_⟩
  simp

/-- The diagonal kernel lies over exactly the original selected point. -/
theorem diagonalKernel_comap :
    Ideal.comap (algebraMap R (CoefficientRing k R p))
      (RingHom.ker (diagonalEvaluation k R p).toRingHom) = p.asIdeal := by
  ext r
  change diagonalEvaluation k R p (movingValue k R p r) = 0 ↔ r ∈ p.asIdeal
  rw [diagonalEvaluation_movingValue, Ideal.algebraMap_residueField_eq_zero]

end QuadraticIncidence.ClosedPoint
