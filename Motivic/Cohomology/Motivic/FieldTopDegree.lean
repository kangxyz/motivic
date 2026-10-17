/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.FieldCycleEvaluation
public import Motivic.Cohomology.Motivic.FiniteHypercohomology
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Vanishing and integral reduction in the top field degree

The literal signed reduced-transfer complex has no terms above its weight.
The proved field evaluation comparison therefore gives actual integral
`H^{p,q}(k, ℤ) = 0` for `p > q`. The original positive Bockstein sequence
implies the same vanishing with finite coefficients, and identifies actual
`H^{q,q}(k, ℤ/n)` with integral `H^{q,q}(k, ℤ)` modulo its subgroup of
`n`-multiples. The equivalence sends the original integral reduction to the
literal integral coset.

These statements hold for every field and every natural coefficient level,
including zero, one, composite levels, and levels divisible by the
characteristic. They compute neither the integral top group nor Milnor
K-theory, and make no assertion for a general smooth scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace Motivic.FieldTopDegree

variable (k : Type u) [Field k]

/-- The actual signed raw field complex has no term strictly above its weight. -/
theorem isZero_raw_X (p : ℤ) (q : ℕ) (hp : (q : ℤ) < p) :
    IsZero ((motivicRawBaseComplex k q).X p) := by
  let E := PresheafWithTransfers.toPresheaf k ⋙
    (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj
      (op (SmoothSite.base (Spec (.of k))))
  change IsZero (E.obj ((PresheafWithTransfers.singularCochainComplex
    (PresheafWithTransfers.reducedTorus k q) 0).X (p + -(q : ℤ))))
  exact E.map_isZero (PresheafWithTransfers.isZero_singularCochainComplex_X
    (PresheafWithTransfers.reducedTorus k q) 0 _ (by omega))

/-- Actual raw homology above the weight vanishes by its zero middle term. -/
theorem isZero_raw_homology (p : ℤ) (q : ℕ) (hp : (q : ℤ) < p) :
    IsZero ((motivicRawBaseComplex k q).homology p) :=
  ((motivicRawBaseComplex k q).sc p).isZero_homology_of_isZero_X₂
    (isZero_raw_X k p q hp)

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Genuine derived integral field cohomology vanishes strictly above the weight. -/
theorem subsingleton_integral_above (p : ℤ) (q : ℕ) (hp : (q : ℤ) < p) :
    Subsingleton (motivicCohomology k p q (SmoothSite.base (Spec (.of k)))) := by
  let := AddCommGrpCat.subsingleton_of_isZero (isZero_raw_homology k p q hp)
  exact (motivicRawBaseEvaluationComparison k p q).injective.subsingleton

/-- The original positive Bockstein is zero in and above the top degree. -/
theorem bockstein_eq_zero (p : ℤ) (q n : ℕ) (hp : (q : ℤ) ≤ p)
    (x : motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k)))) :
    motivicBaseBockstein k p q n x = 0 :=
  @Subsingleton.elim _ (subsingleton_integral_above k (p + 1) q (by omega)) _ _

/-- Original integral reduction is onto in and above the top degree. -/
theorem integralReduction_surjective_of_le (p : ℤ) (q n : ℕ) (hp : (q : ℤ) ≤ p) :
    Function.Surjective (motivicBaseIntegralReduction k p q n) := by
  intro x
  exact (motivicBase_exact_reduction_bockstein k p q n x).1
    (bockstein_eq_zero k p q n hp x)

/-- Actual derived finite field cohomology also vanishes strictly above the weight. -/
theorem subsingleton_finite_above (p : ℤ) (q n : ℕ) (hp : (q : ℤ) < p) :
    Subsingleton (motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k)))) := by
  let := subsingleton_integral_above k p q hp
  exact (integralReduction_surjective_of_le k p q n hp.le).subsingleton

/-- Every actual finite top-degree class lifts under the original integral reduction. -/
theorem integralReduction_surjective (q n : ℕ) :
    Function.Surjective (motivicBaseIntegralReduction k (q : ℤ) q n) :=
  integralReduction_surjective_of_le k q q n le_rfl

/-- The kernel at the top is the same exact `n`-multiple kernel as in the original sequence. -/
theorem integralReduction_eq_zero_iff (q n : ℕ)
    (x : motivicCohomology k (q : ℤ) q (SmoothSite.base (Spec (.of k)))) :
    motivicBaseIntegralReduction k (q : ℤ) q n x = 0 ↔
      ∃ y : motivicCohomology k (q : ℤ) q (SmoothSite.base (Spec (.of k))), n • y = x :=
  motivicBase_exact_mul_reduction k q q n x

/-- Every actual finite top-degree class is annihilated by the coefficient level. -/
theorem nsmul_eq_zero (q n : ℕ)
    (x : motivicFiniteCohomology k (q : ℤ) q n (SmoothSite.base (Spec (.of k)))) :
    n • x = 0 := by
  obtain ⟨y, rfl⟩ := integralReduction_surjective k q n x
  rw [← map_nsmul]
  exact (motivicBase_exact_mul_reduction k q q n).apply_apply_eq_zero y

/-- The literal subgroup of `n`-multiples in actual integral top-degree cohomology. -/
def integralMultiples (q n : ℕ) :
    AddSubgroup (motivicCohomology k (q : ℤ) q (SmoothSite.base (Spec (.of k)))) :=
  (n • AddMonoidHom.id
    (motivicCohomology k (q : ℤ) q (SmoothSite.base (Spec (.of k))))).range

/-- Membership in the subgroup is the actual integral multiplication equation. -/
theorem mem_integralMultiples (q n : ℕ)
    (x : motivicCohomology k (q : ℤ) q (SmoothSite.base (Spec (.of k)))) :
    x ∈ integralMultiples k q n ↔
      ∃ y : motivicCohomology k (q : ℤ) q (SmoothSite.base (Spec (.of k))), n • y = x :=
  Iff.rfl

/-- The original integral reduction has precisely this subgroup as its kernel. -/
theorem integralReduction_ker (q n : ℕ) :
    (motivicBaseIntegralReduction k (q : ℤ) q n).ker = integralMultiples k q n := by
  ext x
  exact integralReduction_eq_zero_iff k q n x

/-- Integral top-degree cohomology modulo its actual subgroup of `n`-multiples. -/
abbrev integralModulo (q n : ℕ) :=
  motivicCohomology k (q : ℤ) q (SmoothSite.base (Spec (.of k))) ⧸ integralMultiples k q n

/-- The first isomorphism theorem for the original top-degree coefficient reduction. -/
def quotientToFiniteEquiv (q n : ℕ) : integralModulo k q n ≃+
    motivicFiniteCohomology k (q : ℤ) q n (SmoothSite.base (Spec (.of k))) :=
  (QuotientAddGroup.quotientAddEquivOfEq (integralReduction_ker k q n).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (motivicBaseIntegralReduction k (q : ℤ) q n) (integralReduction_surjective k q n))

/-- Actual finite top-degree cohomology is canonically integral top cohomology modulo `n`. -/
def topDegreeFiniteEquiv (q n : ℕ) :
    motivicFiniteCohomology k (q : ℤ) q n (SmoothSite.base (Spec (.of k))) ≃+
      integralModulo k q n :=
  (quotientToFiniteEquiv k q n).symm

/-- The inverse of the top-degree comparison uses the original integral reduction. -/
theorem topDegreeFiniteEquiv_symm_mk (q n : ℕ)
    (x : motivicCohomology k (q : ℤ) q (SmoothSite.base (Spec (.of k)))) :
    (topDegreeFiniteEquiv k q n).symm
        (QuotientAddGroup.mk x : integralModulo k q n) =
      motivicBaseIntegralReduction k (q : ℤ) q n x := rfl

/-- The comparison sends integral reduction to its own coset without changing conventions. -/
theorem topDegreeFiniteEquiv_integralReduction (q n : ℕ)
    (x : motivicCohomology k (q : ℤ) q (SmoothSite.base (Spec (.of k)))) :
    topDegreeFiniteEquiv k q n (motivicBaseIntegralReduction k (q : ℤ) q n x) =
      (QuotientAddGroup.mk x : integralModulo k q n) := by
  rw [← topDegreeFiniteEquiv_symm_mk, AddEquiv.apply_symm_apply]

end Motivic.FieldTopDegree
