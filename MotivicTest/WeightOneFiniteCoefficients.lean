/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Coefficients.Finite.WeightOne
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Rat
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual finite weight-one cohomology

These tests use the original derived groups, the original integral reduction,
and the literal multiplicative quotient of field units by powers. They cover
all natural levels, level one, composite levels, and characteristic-dividing
levels. The rejecting axiom audit follows all geometric and coefficient
comparison dependencies, allowing only the standard Lean foundations.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic
open Motivic.WeightOneHomologyNorm Motivic.WeightOneFiniteCoefficients

universe w u

namespace MotivicTest.WeightOneFiniteCoefficients

variable (k : Type u) [Field k]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- No restriction on the coefficient level or the field characteristic is required. -/
def actual_equivalence_all_levels (n : ℕ) :
    motivicFiniteCohomology k 1 1 n (SmoothSite.base (Spec (.of k))) ≃+
      Additive (kˣ ⧸ (powMonoidHom n).range) := weightOneFiniteEquiv k n

/-- The integral vanishing is a proved consequence of the actual raw complex. -/
theorem actual_integral_two_vanishes
    (x : motivicCohomology k 2 1 (SmoothSite.base (Spec (.of k)))) : x = 0 :=
  @Subsingleton.elim _ (subsingleton_integral_two k) _ _

/-- The original integral-to-finite map is surjective. -/
theorem actual_reduction_surjective (n : ℕ) :
    Function.Surjective (motivicBaseIntegralReduction k 1 1 n) :=
  integralReduction_surjective k n

/-- The original map has kernel exactly the integral multiples of the level. -/
theorem actual_reduction_kernel_multiples (n : ℕ)
    (x : motivicCohomology k 1 1 (SmoothSite.base (Spec (.of k)))) :
    motivicBaseIntegralReduction k 1 1 n x = 0 ↔
      ∃ y : motivicCohomology k 1 1 (SmoothSite.base (Spec (.of k))), n • y = x :=
  motivicBase_exact_mul_reduction k 1 1 n x

/-- In geometric norm coordinates this is precisely the subgroup of `n`th powers. -/
theorem actual_reduction_kernel_powers (n : ℕ)
    (x : motivicCohomology k 1 1 (SmoothSite.base (Spec (.of k)))) :
    motivicBaseIntegralReduction k 1 1 n x = 0 ↔
      ∃ a : kˣ, a ^ n = (motivicNorm k x).toMul :=
  integralReduction_eq_zero_iff_norm_power k n x

/-- The actual reduction takes the norm to its own unit coset, without inversion. -/
theorem actual_reduction_norm_coset (n : ℕ)
    (x : motivicCohomology k 1 1 (SmoothSite.base (Spec (.of k)))) :
    actual_equivalence_all_levels k n (motivicBaseIntegralReduction k 1 1 n x) =
      Additive.ofMul (QuotientGroup.mk (motivicNorm k x).toMul :
        kˣ ⧸ (powMonoidHom n).range) :=
  weightOneFiniteEquiv_integralReduction k n x

/-- Inverse cosets retain the actual rational graph class and its comparison. -/
theorem actual_inverse_graph (n : ℕ) (a : kˣ) :
    (actual_equivalence_all_levels k n).symm
        (Additive.ofMul (QuotientGroup.mk a : kˣ ⧸ (powMonoidHom n).range)) =
      motivicBaseIntegralReduction k 1 1 n
        ((motivicRawBaseEvaluationComparison k 1 1).symm (graphUnitClass k a)) :=
  weightOneFiniteEquiv_symm_graph k n a

/-- The actual level-one finite group vanishes. -/
theorem actual_level_one_zero
    (x : motivicFiniteCohomology k 1 1 1 (SmoothSite.base (Spec (.of k)))) : x = 0 :=
  @Subsingleton.elim _ (subsingleton_level_one k) _ _

/-- Level one is covered by the same literal units-modulo-powers equivalence. -/
def actual_level_one_equivalence :
    motivicFiniteCohomology k 1 1 1 (SmoothSite.base (Spec (.of k))) ≃+
      Additive (kˣ ⧸ (powMonoidHom 1).range) := weightOneFiniteEquiv k 1

/-- Composite levels require no primality or invertibility assumption. -/
def actual_level_twelve_equivalence :
    motivicFiniteCohomology k 1 1 12 (SmoothSite.base (Spec (.of k))) ≃+
      Additive (kˣ ⧸ (powMonoidHom 12).range) := weightOneFiniteEquiv k 12

/-- Actual composite-level classes are killed by that composite level. -/
theorem actual_level_twelve_torsion
    (x : motivicFiniteCohomology k 1 1 12 (SmoothSite.base (Spec (.of k)))) : 12 • x = 0 :=
  nsmul_eq_zero k 12 x

/-- The signed positive Bockstein used in the original sequence vanishes in degree one. -/
theorem actual_positive_bockstein_zero (n : ℕ)
    (x : motivicFiniteCohomology k 1 1 n (SmoothSite.base (Spec (.of k)))) :
    motivicBaseBockstein k 1 1 n x = 0 := bockstein_eq_zero k n x

section CharacteristicTwo

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of (ZMod 2)))) AddCommGrpCat.{1})]

/-- The coefficient level equals the characteristic, so no prime-to-characteristic caveat hides. -/
def actual_characteristic_two_level_two :
    motivicFiniteCohomology (ZMod 2) 1 1 2
        (SmoothSite.base (Spec (.of (ZMod 2)))) ≃+
      Additive ((ZMod 2)ˣ ⧸ (powMonoidHom 2).range) :=
  weightOneFiniteEquiv (ZMod 2) 2

/-- A composite coefficient level divisible by the characteristic is covered too. -/
def actual_characteristic_two_level_six :
    motivicFiniteCohomology (ZMod 2) 1 1 6
        (SmoothSite.base (Spec (.of (ZMod 2)))) ≃+
      Additive ((ZMod 2)ˣ ⧸ (powMonoidHom 6).range) :=
  weightOneFiniteEquiv (ZMod 2) 6

end CharacteristicTwo

section RationalSquareClass

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of ℚ))) AddCommGrpCat.{1})]

/-- The actual class of `-1` over the rationals is nonzero modulo two. -/
theorem actual_rational_minus_one_nonzero :
    unitReduction ℚ 2 (Additive.ofMul (-1 : ℚˣ)) ≠ 0 := by
  intro h
  obtain ⟨a, ha⟩ := (unitReduction_eq_zero_iff ℚ 2 (Additive.ofMul (-1 : ℚˣ))).1 h
  have ha' : (a : ℚ) ^ 2 = -1 := by
    simpa using congrArg (fun b : ℚˣ => (b : ℚ)) ha
  have hs := sq_nonneg (a : ℚ)
  rw [ha'] at hs
  norm_num at hs

end RationalSquareClass

open Lean in
run_cmd do
  for name in #[``powerSubgroup, ``unitsModuloPowers, ``mem_powerSubgroup,
      ``isZero_raw_homology_two, ``subsingleton_integral_two, ``bockstein_eq_zero,
      ``integralReduction_surjective, ``unitReduction, ``unitReduction_surjective,
      ``unitReduction_eq_zero_iff, ``integralReduction_eq_zero_iff_norm_power,
      ``nsmul_eq_zero, ``unitReduction_ker, ``quotientToFiniteMulEquiv,
      ``weightOneFiniteEquiv, ``weightOneFiniteEquiv_symm_mk,
      ``weightOneFiniteEquiv_unitReduction, ``weightOneFiniteEquiv_integralReduction,
      ``weightOneFiniteEquiv_symm_graph, ``subsingleton_level_one,
      ``actual_equivalence_all_levels, ``actual_integral_two_vanishes,
      ``actual_reduction_surjective, ``actual_reduction_kernel_multiples,
      ``actual_reduction_kernel_powers, ``actual_reduction_norm_coset,
      ``actual_inverse_graph, ``actual_level_one_zero, ``actual_level_one_equivalence,
      ``actual_level_twelve_equivalence, ``actual_level_twelve_torsion,
      ``actual_positive_bockstein_zero, ``actual_characteristic_two_level_two,
      ``actual_characteristic_two_level_six, ``actual_rational_minus_one_nonzero] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual finite weight-one cohomology uses only standard Lean foundations."

end MotivicTest.WeightOneFiniteCoefficients
