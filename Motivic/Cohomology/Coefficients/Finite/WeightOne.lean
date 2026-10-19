/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.Equivalence
public import Motivic.Cohomology.Coefficients.Finite.Hypercohomology
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Actual finite-coefficient weight-one cohomology of a field

The actual raw complex has zero term in degree two, so its genuine derived
field comparison proves `H^{2,1}(k, ℤ) = 0`. The existing coefficient exact
sequence therefore identifies actual finite `H^{1,1}` with the cokernel of
multiplication by the level on actual integral `H^{1,1}`. The proved geometric
norm identifies this cokernel canonically with units modulo powers.

The construction works for every natural level, including one, composite
levels, and levels divisible by the characteristic. Its reduction formula
retains the original norm and graph conventions, with no inverse sign.
No assertion about degree zero or roots of unity is made here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w u

namespace Motivic.WeightOneFiniteCoefficients
open _root_.AlgebraicGeometry.Scheme

open WeightOneHomologyNorm WeightOneEquivalence

variable (k : Type u) [Field k]

/-- The subgroup consists of genuine `n`th powers of units of the original field. -/
def powerSubgroup (n : ℕ) : Subgroup kˣ := (powMonoidHom n).range

/-- The usual multiplicative quotient of field units by their `n`th powers. -/
abbrev unitsModuloPowers (n : ℕ) := kˣ ⧸ powerSubgroup k n

/-- Membership retains the literal power operation on field units. -/
theorem mem_powerSubgroup (n : ℕ) (a : kˣ) :
    a ∈ powerSubgroup k n ↔ ∃ b : kˣ, b ^ n = a := Iff.rfl

/-- Degree-two raw weight-one homology vanishes because its actual middle term does. -/
theorem isZero_raw_homology_two : IsZero ((motivicRawBaseComplex k 1).homology 2) :=
  ((motivicRawBaseComplex k 1).sc 2).isZero_homology_of_isZero_X₂ (isZero_raw_X_two k)

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Actual integral `H^{2,1}` of any field is zero, by the proved raw comparison. -/
theorem subsingleton_integral_two :
    Subsingleton (motivicCohomology k 2 1 (SmoothSite.base (Spec (.of k)))) := by
  let := AddCommGrpCat.subsingleton_of_isZero (isZero_raw_homology_two k)
  exact (motivicRawBaseEvaluationComparison k 2 1).injective.subsingleton

/-- The original positive Bockstein from degree one is zero. -/
theorem bockstein_eq_zero (n : ℕ)
    (x : motivicFiniteCohomology k 1 1 n (SmoothSite.base (Spec (.of k)))) :
    motivicBaseBockstein k 1 1 n x = 0 := by
  exact @Subsingleton.elim (motivicCohomology k 2 1 (SmoothSite.base (Spec (.of k))))
    (subsingleton_integral_two k) _ _

/-- Every actual finite degree-one class is the reduction of an integral class. -/
theorem integralReduction_surjective (n : ℕ) :
    Function.Surjective (motivicBaseIntegralReduction k 1 1 n) := by
  intro x
  exact (motivicBase_exact_reduction_bockstein k 1 1 n x).1 (bockstein_eq_zero k n x)

/-- Reduce the actual integral class of a unit, using the proved geometric norm inverse. -/
def unitReduction (n : ℕ) : Additive kˣ →+
    motivicFiniteCohomology k 1 1 n (SmoothSite.base (Spec (.of k))) :=
  (motivicBaseIntegralReduction k 1 1 n).comp (weightOneEquiv k).symm.toAddMonoidHom

/-- Every actual finite class is represented by the original graph of a unit. -/
theorem unitReduction_surjective (n : ℕ) : Function.Surjective (unitReduction k n) :=
  (integralReduction_surjective k n).comp (weightOneEquiv k).symm.surjective

/-- A unit reduces to zero precisely when it is an actual `n`th power. -/
theorem unitReduction_eq_zero_iff (n : ℕ) (a : Additive kˣ) :
    unitReduction k n a = 0 ↔ ∃ b : kˣ, b ^ n = a.toMul := by
  change motivicBaseIntegralReduction k 1 1 n ((weightOneEquiv k).symm a) = 0 ↔ _
  rw [motivicBase_exact_mul_reduction k 1 1 n]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(weightOneEquiv k y).toMul, ?_⟩
    have h := congrArg (weightOneEquiv k) hy
    rw [map_nsmul, AddEquiv.apply_symm_apply] at h
    exact congrArg Additive.toMul h
  · rintro ⟨b, hb⟩
    refine ⟨(weightOneEquiv k).symm (Additive.ofMul b),
      (weightOneEquiv k).injective ?_⟩
    rw [map_nsmul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact congrArg Additive.ofMul hb

/-- The kernel of original integral reduction is detected by the actual geometric norm. -/
theorem integralReduction_eq_zero_iff_norm_power (n : ℕ)
    (x : motivicCohomology k 1 1 (SmoothSite.base (Spec (.of k)))) :
    motivicBaseIntegralReduction k 1 1 n x = 0 ↔
      ∃ b : kˣ, b ^ n = (motivicNorm k x).toMul := by
  have h := unitReduction_eq_zero_iff k n (weightOneEquiv k x)
  change motivicBaseIntegralReduction k 1 1 n
    ((weightOneEquiv k).symm (weightOneEquiv k x)) = 0 ↔
      ∃ b : kˣ, b ^ n = (motivicNorm k x).toMul at h
  rwa [AddEquiv.symm_apply_apply] at h

/-- Every actual finite weight-one class is annihilated by its coefficient level. -/
theorem nsmul_eq_zero (n : ℕ)
    (x : motivicFiniteCohomology k 1 1 n (SmoothSite.base (Spec (.of k)))) :
    n • x = 0 := by
  obtain ⟨y, rfl⟩ := integralReduction_surjective k n x
  rw [← map_nsmul]
  exact (motivicBase_exact_mul_reduction k 1 1 n).apply_apply_eq_zero y

/-- The multiplicative form of the actual reduction has exactly the power subgroup as kernel. -/
theorem unitReduction_ker (n : ℕ) :
    (unitReduction k n).toMultiplicativeRight.ker = powerSubgroup k n := by
  ext a
  exact unitReduction_eq_zero_iff k n (Additive.ofMul a)

/-- The first isomorphism theorem for the original reduction, in multiplicative notation. -/
def quotientToFiniteMulEquiv (n : ℕ) : unitsModuloPowers k n ≃*
    Multiplicative (motivicFiniteCohomology k 1 1 n (SmoothSite.base (Spec (.of k)))) :=
  (QuotientGroup.quotientMulEquivOfEq (unitReduction_ker k n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (unitReduction k n).toMultiplicativeRight
      (by
        intro x
        obtain ⟨a, ha⟩ := unitReduction_surjective k n x.toAdd
        exact ⟨a.toMul, congrArg Multiplicative.ofAdd ha⟩))

/-- Actual finite weight-one motivic cohomology is units modulo `n`th powers. -/
def weightOneFiniteEquiv (n : ℕ) :
    motivicFiniteCohomology k 1 1 n (SmoothSite.base (Spec (.of k))) ≃+
      Additive (unitsModuloPowers k n) :=
  (quotientToFiniteMulEquiv k n).symm.toAdditiveRight

/-- The inverse sends a literal unit coset to the actual reduction of its integral graph class. -/
theorem weightOneFiniteEquiv_symm_mk (n : ℕ) (a : kˣ) :
    (weightOneFiniteEquiv k n).symm
        (Additive.ofMul (QuotientGroup.mk a : unitsModuloPowers k n)) =
      unitReduction k n (Additive.ofMul a) := rfl

/-- Reduction of a unit is its own coset, with no sign or inverse twist. -/
theorem weightOneFiniteEquiv_unitReduction (n : ℕ) (a : kˣ) :
    weightOneFiniteEquiv k n (unitReduction k n (Additive.ofMul a)) =
      Additive.ofMul (QuotientGroup.mk a : unitsModuloPowers k n) := by
  rw [← weightOneFiniteEquiv_symm_mk, AddEquiv.apply_symm_apply]

/-- The equivalence respects the original integral reduction and geometric norm. -/
theorem weightOneFiniteEquiv_integralReduction (n : ℕ)
    (x : motivicCohomology k 1 1 (SmoothSite.base (Spec (.of k)))) :
    weightOneFiniteEquiv k n (motivicBaseIntegralReduction k 1 1 n x) =
      Additive.ofMul (QuotientGroup.mk (motivicNorm k x).toMul : unitsModuloPowers k n) := by
  have h := weightOneFiniteEquiv_unitReduction k n (weightOneEquiv k x).toMul
  change weightOneFiniteEquiv k n
    (motivicBaseIntegralReduction k 1 1 n ((weightOneEquiv k).symm (weightOneEquiv k x))) =
      Additive.ofMul (QuotientGroup.mk (motivicNorm k x).toMul : unitsModuloPowers k n) at h
  rwa [AddEquiv.symm_apply_apply] at h

/-- A unit representative maps to its original geometric graph under the actual comparison. -/
theorem weightOneFiniteEquiv_symm_graph (n : ℕ) (a : kˣ) :
    (weightOneFiniteEquiv k n).symm
        (Additive.ofMul (QuotientGroup.mk a : unitsModuloPowers k n)) =
      motivicBaseIntegralReduction k 1 1 n
        ((motivicRawBaseEvaluationComparison k 1 1).symm (graphUnitClass k a)) := by
  rw [weightOneFiniteEquiv_symm_mk]
  change motivicBaseIntegralReduction k 1 1 n
    ((weightOneEquiv k).symm (Additive.ofMul a)) = _
  rw [weightOneEquiv_symm_apply]
  rfl

/-- Level one of the actually defined finite group vanishes. -/
theorem subsingleton_level_one :
    Subsingleton (motivicFiniteCohomology k 1 1 1 (SmoothSite.base (Spec (.of k)))) :=
  subsingleton_motivicFiniteCohomology_base_one k 1 1

end Motivic.WeightOneFiniteCoefficients
