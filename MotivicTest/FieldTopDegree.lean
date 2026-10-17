/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.FieldTopDegree
public import Mathlib.Algebra.Field.ZMod
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual base-field top-degree reduction

The consumers use the original derived integral and finite groups, the
original positive Bockstein, and the original integral reduction. They cover
arbitrary weights, the boundary weights zero and two, levels zero and one,
composite levels, and characteristic-dividing levels. The rejecting audit
checks every declaration in the implementation and these consumers.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic Motivic.FieldTopDegree

universe w u

namespace MotivicTest.FieldTopDegree

variable (k : Type u) [Field k]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- All actual integral groups strictly above the weight vanish. -/
theorem actual_integral_above (p : ℤ) (q : ℕ) (hp : (q : ℤ) < p)
    (x : motivicCohomology k p q (SmoothSite.base (Spec (.of k)))) : x = 0 :=
  @Subsingleton.elim _ (subsingleton_integral_above k p q hp) _ _

/-- The same sharp bound holds for actual finite cohomology at every level. -/
theorem actual_finite_above (p : ℤ) (q n : ℕ) (hp : (q : ℤ) < p)
    (x : motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k)))) : x = 0 :=
  @Subsingleton.elim _ (subsingleton_finite_above k p q n hp) _ _

/-- This is the original field reduction rather than a replacement projection. -/
theorem actual_top_reduction_surjective (q n : ℕ) :
    Function.Surjective (motivicBaseIntegralReduction k (q : ℤ) q n) :=
  integralReduction_surjective k q n

/-- This is the literal integral quotient, with the subgroup exposed. -/
def actual_top_equivalence (q n : ℕ) :
    motivicFiniteCohomology k (q : ℤ) q n (SmoothSite.base (Spec (.of k))) ≃+
      (motivicCohomology k (q : ℤ) q (SmoothSite.base (Spec (.of k))) ⧸
        (n • AddMonoidHom.id
          (motivicCohomology k (q : ℤ) q (SmoothSite.base (Spec (.of k))))).range) :=
  topDegreeFiniteEquiv k q n

/-- The equivalence preserves the original integral reduction and its representative. -/
theorem actual_top_reduction_coset (q n : ℕ)
    (x : motivicCohomology k (q : ℤ) q (SmoothSite.base (Spec (.of k)))) :
    actual_top_equivalence k q n (motivicBaseIntegralReduction k (q : ℤ) q n x) =
      (QuotientAddGroup.mk x : integralModulo k q n) :=
  topDegreeFiniteEquiv_integralReduction k q n x

/-- The inverse is also pinned to the original map, so the isomorphism is not arbitrary. -/
theorem actual_top_inverse_coset (q n : ℕ)
    (x : motivicCohomology k (q : ℤ) q (SmoothSite.base (Spec (.of k)))) :
    (actual_top_equivalence k q n).symm
        (QuotientAddGroup.mk x : integralModulo k q n) =
      motivicBaseIntegralReduction k (q : ℤ) q n x :=
  topDegreeFiniteEquiv_symm_mk k q n x

/-- The original positive Bockstein is zero at the exact boundary degree. -/
theorem actual_top_bockstein_zero (q n : ℕ)
    (x : motivicFiniteCohomology k (q : ℤ) q n (SmoothSite.base (Spec (.of k)))) :
    motivicBaseBockstein k (q : ℤ) q n x = 0 :=
  bockstein_eq_zero k q q n le_rfl x

/-- Weight zero includes its first excluded integral degree. -/
theorem actual_weight_zero_integral_one
    (x : motivicCohomology k 1 0 (SmoothSite.base (Spec (.of k)))) : x = 0 :=
  actual_integral_above k 1 0 (by decide) x

/-- Weight zero includes its first excluded finite degree, without a level restriction. -/
theorem actual_weight_zero_finite_one (n : ℕ)
    (x : motivicFiniteCohomology k 1 0 n (SmoothSite.base (Spec (.of k)))) : x = 0 :=
  actual_finite_above k 1 0 n (by decide) x

/-- Even level zero is covered by the top-degree integral quotient theorem. -/
def actual_weight_zero_level_zero :
    motivicFiniteCohomology k 0 0 0 (SmoothSite.base (Spec (.of k))) ≃+
      integralModulo k 0 0 := topDegreeFiniteEquiv k 0 0

/-- Level one is covered without any nontriviality assumption on the quotient. -/
def actual_weight_zero_level_one :
    motivicFiniteCohomology k 0 0 1 (SmoothSite.base (Spec (.of k))) ≃+
      integralModulo k 0 1 := topDegreeFiniteEquiv k 0 1

/-- Weight two includes its first excluded integral degree. -/
theorem actual_weight_two_integral_three
    (x : motivicCohomology k 3 2 (SmoothSite.base (Spec (.of k)))) : x = 0 :=
  actual_integral_above k 3 2 (by decide) x

/-- Weight two includes its first excluded finite degree at a composite level. -/
theorem actual_weight_two_finite_three
    (x : motivicFiniteCohomology k 3 2 12 (SmoothSite.base (Spec (.of k)))) : x = 0 :=
  actual_finite_above k 3 2 12 (by decide) x

/-- The top weight-two statement uses genuine integral classes, without a Milnor identification. -/
def actual_weight_two_level_twelve :
    motivicFiniteCohomology k 2 2 12 (SmoothSite.base (Spec (.of k))) ≃+
      integralModulo k 2 12 := topDegreeFiniteEquiv k 2 12

/-- A composite coefficient level kills all actual top weight-two classes. -/
theorem actual_weight_two_level_twelve_torsion
    (x : motivicFiniteCohomology k 2 2 12 (SmoothSite.base (Spec (.of k)))) : 12 • x = 0 :=
  nsmul_eq_zero k 2 12 x

/-- The actual top weight-two kernel is exactly the integral twelve-multiple subgroup. -/
theorem actual_weight_two_kernel_twelve
    (x : motivicCohomology k 2 2 (SmoothSite.base (Spec (.of k)))) :
    motivicBaseIntegralReduction k 2 2 12 x = 0 ↔
      ∃ y : motivicCohomology k 2 2 (SmoothSite.base (Spec (.of k))), 12 • y = x :=
  integralReduction_eq_zero_iff k 2 12 x

section CharacteristicTwo

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of (ZMod 2)))) AddCommGrpCat.{1})]

/-- The top weight-two theorem includes a level equal to the characteristic. -/
def actual_characteristic_two_level_two :
    motivicFiniteCohomology (ZMod 2) 2 2 2
        (SmoothSite.base (Spec (.of (ZMod 2)))) ≃+
      integralModulo (ZMod 2) 2 2 := topDegreeFiniteEquiv (ZMod 2) 2 2

/-- Composite levels divisible by the characteristic are included as well. -/
def actual_characteristic_two_level_six :
    motivicFiniteCohomology (ZMod 2) 2 2 6
        (SmoothSite.base (Spec (.of (ZMod 2)))) ≃+
      integralModulo (ZMod 2) 2 6 := topDegreeFiniteEquiv (ZMod 2) 2 6

/-- The vanishing bound still holds when the level is divisible by the characteristic. -/
theorem actual_characteristic_two_finite_three
    (x : motivicFiniteCohomology (ZMod 2) 3 2 6
      (SmoothSite.base (Spec (.of (ZMod 2))))) : x = 0 :=
  actual_finite_above (ZMod 2) 3 2 6 (by decide) x

end CharacteristicTwo

open Lean in
run_cmd do
  for name in #[``isZero_raw_X, ``isZero_raw_homology, ``subsingleton_integral_above,
      ``bockstein_eq_zero, ``integralReduction_surjective_of_le, ``subsingleton_finite_above,
      ``integralReduction_surjective, ``integralReduction_eq_zero_iff, ``nsmul_eq_zero,
      ``integralMultiples, ``mem_integralMultiples, ``integralReduction_ker, ``integralModulo,
      ``quotientToFiniteEquiv, ``topDegreeFiniteEquiv, ``topDegreeFiniteEquiv_symm_mk,
      ``topDegreeFiniteEquiv_integralReduction, ``actual_integral_above, ``actual_finite_above,
      ``actual_top_reduction_surjective, ``actual_top_equivalence, ``actual_top_reduction_coset,
      ``actual_top_inverse_coset, ``actual_top_bockstein_zero, ``actual_weight_zero_integral_one,
      ``actual_weight_zero_finite_one, ``actual_weight_zero_level_zero,
      ``actual_weight_zero_level_one,
      ``actual_weight_two_integral_three, ``actual_weight_two_finite_three,
      ``actual_weight_two_level_twelve, ``actual_weight_two_level_twelve_torsion,
      ``actual_weight_two_kernel_twelve, ``actual_characteristic_two_level_two,
      ``actual_characteristic_two_level_six, ``actual_characteristic_two_finite_three] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual field vanishing and top-degree reduction use only standard Lean foundations."

end MotivicTest.FieldTopDegree
