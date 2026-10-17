/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalNormalizedEndpointNorm
public import Motivic.Cohomology.Motivic.DiagonalBoundaryEvaluation

/-! # Actual all-weight Milnor evaluation on diagonal motivic cohomology

The original norm evaluation kills the genuine reduced singular differential.
It therefore descends through the literal zero-homology quotient to the original
signed raw homology and the original derived diagonal motivic cohomology.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe w u
namespace Motivic.DiagonalMilnorBoundaryDescent
open PresheafWithTransfers DiagonalBoundaryEvaluation DiagonalTopDegree
open WeightOneBoundaryNorm KTheory
variable (k : Type u) [Field k] [CharZero k] (q : ℕ)

/-- Endpoint norms agree for every original signed simplex correspondence. -/
theorem cycleValue_endpoint_eq
    (α : Cor.mk (AlgebraicSimplex.smoothSiteObj k 1) ⟶ DiagonalCycleSymbols.target k q)
    (a b : k) :
    DiagonalPointNorm.cycleValue k q
      ((Cor.graphFunctor k).map (evaluationPoint k a) ≫ α) =
    DiagonalPointNorm.cycleValue k q
      ((Cor.graphFunctor k).map (evaluationPoint k b) ≫ α) := by
  have h : (DiagonalPointNorm.cycleValue k q).comp
        (Preadditive.leftComp (DiagonalCycleSymbols.target k q)
          ((Cor.graphFunctor k).map (evaluationPoint k a))) =
      (DiagonalPointNorm.cycleValue k q).comp
        (Preadditive.leftComp (DiagonalCycleSymbols.target k q)
          ((Cor.graphFunctor k).map (evaluationPoint k b))) := by
    apply Finsupp.addHom_ext'
    intro Z
    apply AddMonoidHom.ext_int
    exact DiagonalBoundarySupport.cycleValue_endpoint_generator_eq Z a b
  exact DFunLike.congr_fun h α

/-- The evaluator kills the actual alternating boundary, including weight zero. -/
theorem degreeZeroNorm_boundary (s : chains k q 1) :
    DiagonalBoundaryEvaluation.degreeZeroNorm k q (boundary k q s) = 0 := by
  obtain ⟨⟨α⟩, rfl⟩ := toReducedTorus_surjective k q
    (Cor.simplexProduct (point k) 1) s
  rw [boundary_eq_endpoints, map_sub,
    DiagonalBoundaryEvaluation.degreeZeroNorm_face_quotient,
    DiagonalBoundaryEvaluation.degreeZeroNorm_face_quotient,
    facePoint_zero, facePoint_one, cycleValue_endpoint_eq k q _ 0 1, sub_self]

/-- The original signed raw top term, evaluated using its actual singular identification. -/
def rawTermNorm : (motivicRawBaseComplex k q).X q →+ MilnorK.K k q :=
  (DiagonalBoundaryEvaluation.degreeZeroNorm k q).comp (topTermIso k q).hom.hom

/-- The actual shifted cochain differential, with its original sign, is annihilated. -/
theorem rawTermNorm_differential (s : (motivicRawBaseComplex k q).X ((q : ℤ) - 1)) :
    rawTermNorm k q ((motivicRawBaseComplex k q).d ((q : ℤ) - 1) q s) = 0 := by
  rw [raw_d_top]
  change DiagonalBoundaryEvaluation.degreeZeroNorm k q
    ((topTermIso k q).hom ((-1 : ℤ) ^ q • (topTermIso k q).inv
      (boundary k q ((previousTermIso k q).hom s)))) = 0
  rw [map_zsmul, Iso.inv_hom_id_apply, map_zsmul, degreeZeroNorm_boundary, smul_zero]

/-- Evaluation on the literal original reduced zero-cycles modulo actual boundaries. -/
def quotientNorm : zeroHomology k q →+ MilnorK.K k q :=
  QuotientAddGroup.lift (boundary k q).range
    (DiagonalBoundaryEvaluation.degreeZeroNorm k q) (by
      rintro _ ⟨s, rfl⟩
      exact degreeZeroNorm_boundary k q s)

@[simp] theorem quotientNorm_mk (s : chains k q 0) :
    quotientNorm k q (QuotientAddGroup.mk s) =
      DiagonalBoundaryEvaluation.degreeZeroNorm k q s := rfl

/-- The descended evaluator on the original signed raw homology. -/
def rawNorm : (motivicRawBaseComplex k q).homology q →+ MilnorK.K k q :=
  (quotientNorm k q).comp (quotientToRawEquiv k q).symm.toAddMonoidHom

@[simp] theorem rawNorm_singularClass (s : chains k q 0) :
    rawNorm k q (singularClass k q s) =
      DiagonalBoundaryEvaluation.degreeZeroNorm k q s := by
  rw [← quotientToRawEquiv_mk]
  change quotientNorm k q ((quotientToRawEquiv k q).symm
    (quotientToRawEquiv k q (QuotientAddGroup.mk s))) = _
  rw [AddEquiv.symm_apply_apply, quotientNorm_mk]

/-- On every actual signed point cycle, descent retains the original residue-field norm. -/
theorem rawNorm_cycleClass (α : point k ⟶ DiagonalCycleSymbols.target k q) :
    rawNorm k q (DiagonalCycleSymbols.cycleClass k q α) =
      DiagonalPointNorm.cycleValue k q α := by
  change rawNorm k q (singularClass k q
    ((toReducedTorus k q).hom.app (op (Cor.simplexProduct (point k) 0))
      (ULift.up ((zeroProductIso k).hom ≫ α)))) = _
  rw [rawNorm_singularClass, DiagonalBoundaryEvaluation.degreeZeroNorm_quotient,
    Iso.inv_hom_id_assoc]

/-- Rational graph classes evaluate to their literal Milnor symbol. -/
@[simp] theorem rawNorm_graphSymbol (a : Fin q → kˣ) :
    rawNorm k q (DiagonalCycleSymbols.graphSymbol k q a) = MilnorK.symbol a := by
  rw [DiagonalCycleSymbols.graphSymbol, rawNorm_cycleClass,
    DiagonalPointNorm.cycleValue_rationalTuple]

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Evaluation on the originally defined derived diagonal motivic cohomology. -/
def motivicNorm : motivicCohomology k q q (SmoothSite.base (Spec (.of k))) →+
    MilnorK.K k q :=
  (quotientNorm k q).comp (quotientToMotivicEquiv k q).symm.toAddMonoidHom

/-- The derived evaluator and original signed raw evaluator agree under the actual comparison. -/
theorem motivicNorm_comparison
    (x : motivicCohomology k q q (SmoothSite.base (Spec (.of k)))) :
    motivicNorm k q x = rawNorm k q (motivicRawBaseEvaluationComparison k q q x) := rfl

end Motivic.DiagonalMilnorBoundaryDescent
