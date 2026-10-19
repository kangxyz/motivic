/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.LengthEuler.Basic
public import Aglib.RingTheory.FiniteLength.FiniteAlgebraLength
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Data.ENat.BigOperators

/-!
# Finite signed lengths across all points of a finite algebra

Restriction along a finite algebra over a Noetherian local ring and localization
at each maximal point preserve finite-length support. The literal all-point
length formula is converted to integers only after proving every length finite.
A common finite set of degrees justifies exchanging the degree and point sums.
The algebra need not be Artinian, local, flat, or a quotient of its base.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace HomologicalComplex.ModuleLengthEuler

set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension along a specified algebra map is the literal tensor
product, with the specified target-ring action on both sides. -/
def finiteAlgebraExtendScalarsEquiv (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (algebraMap A B)).obj M ≃ₗ[B] B ⊗[A] M := by
  let N := (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
  letI : IsScalarTower A B N := ⟨fun a b n => by
    change (a • b) • n = algebraMap A B a • (b • n)
    rw [Algebra.smul_def, mul_smul]⟩
  let e : B ≃ₗ[B] N := LinearEquiv.refl _ _
  exact (TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl A M)).symm

variable (R S : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [CommRing S] [Algebra R S] [Module.Finite R S]

set_option backward.isDefEq.respectTransparency false in
/-- Scalar restriction along the finite algebra preserves finite length. -/
theorem finiteAlgebra_restrict_length_ne_top (M : ModuleCat.{u} S)
    (hM : Module.length S M ≠ ⊤) :
    Module.length R ((ModuleCat.restrictScalars (algebraMap R S)).obj M) ≠ ⊤ := by
  let := Module.compHom M (algebraMap R S)
  have : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  change Module.length R M ≠ ⊤
  exact Module.finiteAlgebra_length_ne_top R S hM

include R in
omit [IsLocalRing R] in
/-- Localization at any maximal point has finite length, including points
outside the support, as witnessed by the actual prime-filtration count. -/
theorem finiteAlgebra_localized_length_ne_top (M : ModuleCat.{u} S)
    (hM : Module.length S M ≠ ⊤) (p : MaximalSpectrum S) :
    Module.length (Localization.AtPrime p.asIdeal)
      ((ModuleCat.extendScalars (algebraMap S (Localization.AtPrime p.asIdeal))).obj M) ≠ ⊤ := by
  have : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  have : IsNoetherian S M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hM)).1
  obtain ⟨D⟩ := Module.nonempty_primeFiltrationFrom (A := S) M ⊥
  rw [(finiteAlgebraExtendScalarsEquiv S (Localization.AtPrime p.asIdeal) M).length_eq]
  rw [D.localized_length_eq_count_of_finiteLength hM p]
  exact ENat.natCast_ne_top _

variable {ι : Type v} (X : ι → ModuleCat.{u} S)

omit [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R S] in
set_option backward.isDefEq.respectTransparency false in
/-- Restriction does not introduce a new nonzero degree. -/
theorem finiteAlgebra_restrict_support_subset :
    Function.support (fun i => Module.length R
      ((ModuleCat.restrictScalars (algebraMap R S)).obj (X i))) ⊆
        Function.support (fun i => Module.length S (X i)) := by
  intro i hi
  contrapose! hi
  simp only [Function.mem_support, not_not] at hi ⊢
  apply Module.length_eq_zero_iff.mpr
  change Subsingleton (X i)
  exact Module.length_eq_zero_iff.mp hi

/-- Localization does not introduce a new nonzero degree. -/
theorem finiteAlgebra_localized_support_subset (p : MaximalSpectrum S) :
    Function.support (fun i => Module.length (Localization.AtPrime p.asIdeal)
      ((ModuleCat.extendScalars (algebraMap S (Localization.AtPrime p.asIdeal))).obj (X i))) ⊆
        Function.support (fun i => Module.length S (X i)) := by
  intro i hi
  contrapose! hi
  simp only [Function.mem_support, not_not] at hi ⊢
  have : Subsingleton (X i) := Module.length_eq_zero_iff.mp hi
  rw [(finiteAlgebraExtendScalarsEquiv S (Localization.AtPrime p.asIdeal) (X i)).length_eq]
  exact Module.length_eq_zero

/-- Finite-length support survives actual restriction along the finite algebra. -/
theorem FiniteLengthSupport.finiteAlgebra_restrict (hX : FiniteLengthSupport X) :
    FiniteLengthSupport (fun i => (ModuleCat.restrictScalars (algebraMap R S)).obj (X i)) where
  finite_length i := finiteAlgebra_restrict_length_ne_top R S (X i) (hX.finite_length i)
  finite_support := hX.finite_support.subset (finiteAlgebra_restrict_support_subset R S X)

include R in
omit [IsLocalRing R] in
/-- Finite-length support survives actual localization at every maximal point. -/
theorem FiniteLengthSupport.finiteAlgebra_localized (hX : FiniteLengthSupport X)
    (p : MaximalSpectrum S) :
    FiniteLengthSupport (fun i =>
      (ModuleCat.extendScalars (algebraMap S (Localization.AtPrime p.asIdeal))).obj (X i)) where
  finite_length i := finiteAlgebra_localized_length_ne_top R S (X i) (hX.finite_length i) p
  finite_support := hX.finite_support.subset (finiteAlgebra_localized_support_subset S X p)

set_option backward.isDefEq.respectTransparency false in
/-- The all-point length formula in integers, with each infinite value excluded
before converting the finite sum to natural numbers. -/
theorem integerLength_finiteAlgebra [Fintype (MaximalSpectrum S)]
    (M : ModuleCat.{u} S) (hM : Module.length S M ≠ ⊤) :
    integerLength ((ModuleCat.restrictScalars (algebraMap R S)).obj M)
        (finiteAlgebra_restrict_length_ne_top R S M hM) =
      ∑ p : MaximalSpectrum S, (Module.finiteAlgebraResidueDegree R S p : ℤ) *
        integerLength
          ((ModuleCat.extendScalars (algebraMap S (Localization.AtPrime p.asIdeal))).obj M)
          (finiteAlgebra_localized_length_ne_top R S M hM p) := by
  let := Module.compHom M (algebraMap R S)
  have : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  have hsum : ∀ p : MaximalSpectrum S, p ∈ (Finset.univ : Finset (MaximalSpectrum S)) →
      Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[S] M) *
          (Module.finiteAlgebraResidueDegree R S p : ℕ∞) ≠ ⊤ := by
    intro p _
    apply WithTop.mul_ne_top _ (ENat.natCast_ne_top _)
    rw [← (finiteAlgebraExtendScalarsEquiv S (Localization.AtPrime p.asIdeal) M).length_eq]
    exact finiteAlgebra_localized_length_ne_top R S M hM p
  unfold integerLength
  change ((Module.length R M).toNat : ℤ) = _
  rw [Module.finiteAlgebra_length_eq_sum R S hM, ENat.toNat_sum hsum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_mul]
  rw [(finiteAlgebraExtendScalarsEquiv S (Localization.AtPrime p.asIdeal) M).length_eq]
  exact mul_comm _ _

/-- Finite signed length sums obey the residue-degree-weighted all-point formula. -/
theorem signedLengthSum_finiteAlgebra [Fintype (MaximalSpectrum S)]
    (sign : ι → ℤ) (hX : FiniteLengthSupport X) :
    signedLengthSum
        (fun i => (ModuleCat.restrictScalars (algebraMap R S)).obj (X i)) sign
        (hX.finiteAlgebra_restrict R S X) =
      ∑ p : MaximalSpectrum S, (Module.finiteAlgebraResidueDegree R S p : ℤ) *
        signedLengthSum
          (fun i => (ModuleCat.extendScalars
            (algebraMap S (Localization.AtPrime p.asIdeal))).obj (X i)) sign
          (hX.finiteAlgebra_localized R S X p) := by
  classical
  let t := hX.finite_support.toFinset
  have ht : Function.support (fun i => Module.length S (X i)) ⊆ t :=
    fun i hi => hX.finite_support.mem_toFinset.mpr hi
  rw [signedLengthSum_eq_sum _ _ _ t
    ((finiteAlgebra_restrict_support_subset R S X).trans ht)]
  conv_rhs =>
    arg 2
    ext p
    rw [signedLengthSum_eq_sum _ _ _ t
      ((finiteAlgebra_localized_support_subset S X p).trans ht), Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext i
    rw [integerLength_finiteAlgebra R S (X i) (hX.finite_length i), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro i _
  exact mul_left_comm _ _ _

end HomologicalComplex.ModuleLengthEuler
