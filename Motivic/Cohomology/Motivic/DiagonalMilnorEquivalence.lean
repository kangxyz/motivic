/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalMilnorNormRetraction
public import Motivic.Cohomology.Motivic.DiagonalPolynomialNormComparisonAll
public import Motivic.Cohomology.Motivic.DiagonalPointPresentation

/-!
# Milnor K-theory and the original diagonal motivic cohomology

The opposite inverse uses actual all-degree finite-extension norm compatibility
and the original integral-support presentation of every finite cycle. It is not
inferred from the retraction. Both equivalences retain the originally defined
raw complex and derived motivic cohomology groups and the existing forward symbol.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe w u
namespace Motivic.DiagonalMilnorEquivalence
open PresheafWithTransfers DiagonalCycleSymbols DiagonalMilnorSymbol
open DiagonalMilnorBoundaryDescent
variable (k : Type u) [Field k] [CharZero k] (q : ℕ)

/-- The actual norm of each original integral point is sent back to its own cycle class. -/
theorem rawSymbol_generatorValue (Z : DiagonalPointNorm.Generator k q) :
    rawSymbol k q (DiagonalPointNorm.generatorValue Z) = cycleClass k q Z.cycle := by
  let : CharZero (DiagonalPointNorm.coordinateRing Z) :=
    charZero_of_injective_algebraMap
      (algebraMap k (DiagonalPointNorm.coordinateRing Z)).injective
  rw [DiagonalPointNorm.generatorValue,
    DiagonalPolynomialNormComparisonAll.rawSymbol_finiteExtensionNorm,
    rawSymbol_symbol, DiagonalPointPresentation.cycleClass_generator]

/-- The full signed original point cycle is recovered, retaining all multiplicities. -/
theorem rawSymbol_cycleValue (α : WeightOnePointNorm.point k ⟶ target k q) :
    rawSymbol k q (DiagonalPointNorm.cycleValue k q α) = cycleClass k q α := by
  classical
  induction α using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add α β hα hβ => simp only [map_add, hα, hβ]
  | single Z n =>
    rw [DiagonalPointNorm.cycleValue_single, map_zsmul, rawSymbol_generatorValue]
    have hs : (Finsupp.single Z n : DiagonalPointNorm.Generator k q →₀ ℤ) = n • Z.cycle := by
      change Finsupp.single Z n = n • Finsupp.single Z (1 : ℤ)
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_zsmul]

/-- The opposite inverse on original raw diagonal homology, proved from actual norm comparison. -/
theorem rawSymbol_rawNorm (x : (motivicRawBaseComplex k q).homology q) :
    rawSymbol k q (rawNorm k q x) = x := by
  obtain ⟨α, rfl⟩ := cycleClass_surjective k q x
  rw [rawNorm_cycleClass, rawSymbol_cycleValue]

/-- The existing forward symbol and actual descended norm are inverse on the original raw group. -/
def rawEquiv : MilnorK.K k q ≃+ (motivicRawBaseComplex k q).homology q where
  toFun := rawSymbol k q
  invFun := rawNorm k q
  left_inv := rawNorm_rawSymbol k q
  right_inv := rawSymbol_rawNorm k q
  map_add' := map_add (rawSymbol k q)

@[simp] theorem rawEquiv_apply (x : MilnorK.K k q) :
    rawEquiv k q x = rawSymbol k q x := rfl

@[simp] theorem rawEquiv_symm_apply (x : (motivicRawBaseComplex k q).homology q) :
    (rawEquiv k q).symm x = rawNorm k q x := rfl

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The opposite inverse on the originally defined derived motivic cohomology group. -/
theorem motivicSymbol_motivicNorm
    (x : motivicCohomology k q q (SmoothSite.base (Spec (.of k)))) :
    motivicSymbol k q (motivicNorm k q x) = x := by
  apply (motivicRawBaseEvaluationComparison k q q).injective
  rw [motivicSymbol_comparison, motivicNorm_comparison, rawSymbol_rawNorm]

/-- Actual all-weight diagonal comparison, with the original forward symbol and norm inverse. -/
def motivicEquiv : MilnorK.K k q ≃+
    motivicCohomology k q q (SmoothSite.base (Spec (.of k))) where
  toFun := motivicSymbol k q
  invFun := motivicNorm k q
  left_inv := motivicNorm_motivicSymbol k q
  right_inv := motivicSymbol_motivicNorm k q
  map_add' := map_add (motivicSymbol k q)

@[simp] theorem motivicEquiv_apply (x : MilnorK.K k q) :
    motivicEquiv k q x = motivicSymbol k q x := rfl

@[simp] theorem motivicEquiv_symm_apply
    (x : motivicCohomology k q q (SmoothSite.base (Spec (.of k)))) :
    (motivicEquiv k q).symm x = motivicNorm k q x := rfl

end Motivic.DiagonalMilnorEquivalence
