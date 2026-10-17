/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.RawFieldChange
public import Motivic.Cohomology.Motivic.FiniteHypercohomology

/-!
# Field maps on the actual derived motivic groups

The original signed cycle field-change cochain map induces maps on actual
integral and finite motivic cohomology at the two base fields. The construction
uses the proved field evaluation comparisons and the original coefficient cone.
Integral reduction and the positive Bockstein commute with this map.

The field map is arbitrary. This file does not assert a sheaf inverse-image
comparison or coherence under a tower of changing ground fields.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w u

namespace Motivic

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

/-- The actual evaluated sheaf complexes inherit the original raw cycle map. -/
def motivicBaseComplexMap (q : ℕ) : motivicBaseComplex k q ⟶ motivicBaseComplex L q :=
  (motivicRawBaseComplexIso k q).inv ≫ motivicRawBaseComplexMap φ q ≫
    (motivicRawBaseComplexIso L q).hom

/-- The integral comparison is a commuting square of complete complexes. -/
@[reassoc]
theorem motivicBaseComplexMap_raw (q : ℕ) :
    (motivicRawBaseComplexIso k q).hom ≫ motivicBaseComplexMap φ q =
      motivicRawBaseComplexMap φ q ≫ (motivicRawBaseComplexIso L q).hom := by
  simp [motivicBaseComplexMap]

/-- Actual finite field-change complexes use the same coefficient-cone functor. -/
def motivicBaseFiniteConeMap (q n : ℕ) :
    finiteCoefficients (motivicBaseComplex k q) n ⟶
      finiteCoefficients (motivicBaseComplex L q) n :=
  finiteCoefficients.map n (motivicBaseComplexMap φ q)

/-- The integral-to-finite map commutes already before passing to homology. -/
@[reassoc]
theorem motivicBaseFiniteConeMap_integral (q n : ℕ) :
    finiteCoefficients.integral (motivicBaseComplex k q) n ≫
      motivicBaseFiniteConeMap φ q n =
    motivicBaseComplexMap φ q ≫ finiteCoefficients.integral (motivicBaseComplex L q) n :=
  finiteCoefficients.integral_naturality n (motivicBaseComplexMap φ q)

/-- The actual positive connecting map retains the canonical signed shift. -/
@[reassoc]
theorem motivicBaseFiniteConeMap_bockstein (q n : ℕ) :
    motivicBaseFiniteConeMap φ q n ≫ finiteCoefficients.bockstein (motivicBaseComplex L q) n =
      finiteCoefficients.bockstein (motivicBaseComplex k q) n ≫
        (motivicBaseComplexMap φ q)⟦(1 : ℤ)⟧' :=
  finiteCoefficients.bockstein_naturality n (motivicBaseComplexMap φ q)

private theorem integralHomology_naturality (p : ℤ) (q n : ℕ) :
    finiteCoefficients.integralHomology (motivicBaseComplex k q) n p ≫
      HomologicalComplex.homologyMap (motivicBaseFiniteConeMap φ q n) p =
    HomologicalComplex.homologyMap (motivicBaseComplexMap φ q) p ≫
      finiteCoefficients.integralHomology (motivicBaseComplex L q) n p := by
  simpa only [finiteCoefficients.integralHomology,
    HomologicalComplex.homologyMap_comp] using
      congrArg (fun f => HomologicalComplex.homologyMap f p)
        (motivicBaseFiniteConeMap_integral φ q n)

private theorem bocksteinHomology_naturality (p : ℤ) (q n : ℕ) :
    HomologicalComplex.homologyMap (motivicBaseFiniteConeMap φ q n) p ≫
      finiteCoefficients.bocksteinHomology (motivicBaseComplex L q) n p =
    finiteCoefficients.bocksteinHomology (motivicBaseComplex k q) n p ≫
      HomologicalComplex.homologyMap (motivicBaseComplexMap φ q) (p + 1) := by
  dsimp only [finiteCoefficients.bocksteinHomology]
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    motivicBaseFiniteConeMap_bockstein, HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc]
  congr 1
  exact ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) 0).shiftIso
    1 p (p + 1) (add_comm 1 p)).hom.naturality (motivicBaseComplexMap φ q)

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]

/-- Arbitrary field change on the genuine derived integral motivic groups at the base field. -/
def motivicCohomologyFieldChange (p : ℤ) (q : ℕ) :
    motivicCohomology k p q (SmoothSite.base (Spec (.of k))) →+
      motivicCohomology L p q (SmoothSite.base (Spec (.of L))) :=
  (motivicBaseEvaluationComparison L p q).symm.toAddMonoidHom.comp
    ((HomologicalComplex.homologyMap (motivicBaseComplexMap φ q) p).hom.comp
      (motivicBaseEvaluationComparison k p q).toAddMonoidHom)

/-- The comparison fixes the actual cohomology map, rather than an abstract homomorphism. -/
@[simp]
theorem motivicCohomologyFieldChange_comparison (p : ℤ) (q : ℕ)
    (x : motivicCohomology k p q (SmoothSite.base (Spec (.of k)))) :
    motivicBaseEvaluationComparison L p q (motivicCohomologyFieldChange φ p q x) =
      HomologicalComplex.homologyMap (motivicBaseComplexMap φ q) p
        (motivicBaseEvaluationComparison k p q x) := by
  simp [motivicCohomologyFieldChange]

/-- The same field map is induced by the literal signed cycle map under the raw comparison. -/
theorem motivicCohomologyFieldChange_rawComparison (p : ℤ) (q : ℕ)
    (x : motivicCohomology k p q (SmoothSite.base (Spec (.of k)))) :
    motivicRawBaseEvaluationComparison L p q (motivicCohomologyFieldChange φ p q x) =
      HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ q) p
        (motivicRawBaseEvaluationComparison k p q x) := by
  simp only [motivicRawBaseEvaluationComparison, AddEquiv.trans_apply,
    motivicCohomologyFieldChange_comparison]
  change HomologicalComplex.homologyMap (motivicRawBaseComplexIso L q).inv p
      (HomologicalComplex.homologyMap (motivicBaseComplexMap φ q) p
        (motivicBaseEvaluationComparison k p q x)) =
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ q) p
      (HomologicalComplex.homologyMap (motivicRawBaseComplexIso k q).inv p
        (motivicBaseEvaluationComparison k p q x))
  have h : motivicBaseComplexMap φ q ≫ (motivicRawBaseComplexIso L q).inv =
      (motivicRawBaseComplexIso k q).inv ≫ motivicRawBaseComplexMap φ q := by
    simp [motivicBaseComplexMap]
  exact ConcreteCategory.congr_hom
    (by simpa only [HomologicalComplex.homologyMap_comp] using
      congrArg (fun f => HomologicalComplex.homologyMap f p) h)
    (motivicBaseEvaluationComparison k p q x)

/-- Arbitrary field change with every coefficient level,
including characteristic-dividing levels. -/
def motivicFiniteCohomologyFieldChange (p : ℤ) (q n : ℕ) :
    motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k))) →+
      motivicFiniteCohomology L p q n (SmoothSite.base (Spec (.of L))) :=
  (motivicFiniteBaseConeComparison L p q n).symm.toAddMonoidHom.comp
    ((HomologicalComplex.homologyMap (motivicBaseFiniteConeMap φ q n) p).hom.comp
      (motivicFiniteBaseConeComparison k p q n).toAddMonoidHom)

/-- The finite comparison retains the actual cone of the same integral field map. -/
@[simp]
theorem motivicFiniteCohomologyFieldChange_comparison (p : ℤ) (q n : ℕ)
    (x : motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k)))) :
    motivicFiniteBaseConeComparison L p q n (motivicFiniteCohomologyFieldChange φ p q n x) =
      HomologicalComplex.homologyMap (motivicBaseFiniteConeMap φ q n) p
        (motivicFiniteBaseConeComparison k p q n x) := by
  simp [motivicFiniteCohomologyFieldChange]

/-- The original integral reduction commutes with the actual arbitrary field map. -/
theorem motivicCohomologyFieldChange_integralReduction (p : ℤ) (q n : ℕ)
    (x : motivicCohomology k p q (SmoothSite.base (Spec (.of k)))) :
    motivicFiniteCohomologyFieldChange φ p q n (motivicBaseIntegralReduction k p q n x) =
      motivicBaseIntegralReduction L p q n (motivicCohomologyFieldChange φ p q x) := by
  apply (motivicFiniteBaseConeComparison L p q n).injective
  simp only [motivicFiniteCohomologyFieldChange_comparison,
    motivicBaseIntegralReduction_comparison, motivicCohomologyFieldChange_comparison]
  exact ConcreteCategory.congr_hom (integralHomology_naturality φ p q n)
    (motivicBaseEvaluationComparison k p q x)

/-- The original positive Bockstein commutes in every degree with arbitrary field change. -/
theorem motivicCohomologyFieldChange_bockstein (p : ℤ) (q n : ℕ)
    (x : motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k)))) :
    motivicCohomologyFieldChange φ (p + 1) q (motivicBaseBockstein k p q n x) =
      motivicBaseBockstein L p q n (motivicFiniteCohomologyFieldChange φ p q n x) := by
  apply (motivicBaseEvaluationComparison L (p + 1) q).injective
  simp only [motivicCohomologyFieldChange_comparison, motivicBaseBockstein_comparison,
    motivicFiniteCohomologyFieldChange_comparison]
  exact (ConcreteCategory.congr_hom (bocksteinHomology_naturality φ p q n)
    (motivicFiniteBaseConeComparison k p q n x)).symm

end Motivic
