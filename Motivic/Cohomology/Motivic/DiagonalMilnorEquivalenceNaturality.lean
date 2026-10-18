/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalMilnorEquivalence

/-! # Both directions of the original diagonal comparison preserve field maps and transfer -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe w u
namespace Motivic.DiagonalMilnorEquivalenceNaturality
open PresheafWithTransfers DiagonalMilnorSymbol DiagonalMilnorBoundaryDescent
open DiagonalMilnorEquivalence DiagonalCorestriction
variable {k L : Type u} [Field k] [CharZero k] [Field L] [CharZero L]

/-- The actual inverse evaluator commutes with every original raw field-change map. -/
theorem rawNorm_fieldChange (φ : k →+* L) (q : ℕ)
    (x : (motivicRawBaseComplex k q).homology q) :
    rawNorm L q
        (HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ q) q x) =
      MilnorK.map q φ (rawNorm k q x) := by
  apply rawSymbol_injective L q
  rw [rawSymbol_rawNorm, ← DiagonalFieldChange.rawSymbol_fieldChange, rawSymbol_rawNorm]

/-- The actual inverse evaluator sends finite cycle corestriction to the original Milnor norm. -/
theorem rawNorm_corestriction [Algebra k L] [Module.Finite k L] (q : ℕ)
    (x : (motivicRawBaseComplex L q).homology q) :
    rawNorm k q (corestriction (k := k) (E := L) q x) =
      MilnorK.finiteExtensionNorm k L q (rawNorm L q x) := by
  apply rawSymbol_injective k q
  rw [rawSymbol_rawNorm, DiagonalPolynomialNormComparisonAll.rawSymbol_finiteExtensionNorm,
    rawSymbol_rawNorm]

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]

/-- Original derived field-change naturality for the inverse in every diagonal weight. -/
theorem motivicNorm_fieldChange (φ : k →+* L) (q : ℕ)
    (x : motivicCohomology k q q (SmoothSite.base (Spec (.of k)))) :
    motivicNorm L q (motivicCohomologyFieldChange φ q q x) =
      MilnorK.map q φ (motivicNorm k q x) := by
  rw [motivicNorm_comparison, motivicCohomologyFieldChange_rawComparison,
    rawNorm_fieldChange, motivicNorm_comparison]

/-- The actual derived norm evaluator retains the original finite-field transfer. -/
theorem motivicNorm_corestriction [Algebra k L] [Module.Finite k L] (q : ℕ)
    (x : motivicCohomology L q q (SmoothSite.base (Spec (.of L)))) :
    motivicNorm k q (motivicCorestriction (k := k) (E := L) q x) =
      MilnorK.finiteExtensionNorm k L q (motivicNorm L q x) := by
  rw [motivicNorm_comparison, motivicCorestriction_comparison,
    rawNorm_corestriction, motivicNorm_comparison]

/-- The original derived forward symbol has the finite norm/corestriction square. -/
theorem motivicSymbol_finiteExtensionNorm [Algebra k L] [Module.Finite k L]
    (q : ℕ) (x : MilnorK.K L q) :
    motivicSymbol k q (MilnorK.finiteExtensionNorm k L q x) =
      motivicCorestriction (k := k) (E := L) q (motivicSymbol L q x) := by
  apply (motivicRawBaseEvaluationComparison k q q).injective
  rw [motivicSymbol_comparison, motivicCorestriction_comparison,
    motivicSymbol_comparison, DiagonalPolynomialNormComparisonAll.rawSymbol_finiteExtensionNorm]

end Motivic.DiagonalMilnorEquivalenceNaturality
