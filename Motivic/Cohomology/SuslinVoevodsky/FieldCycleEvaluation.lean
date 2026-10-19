/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SuslinVoevodsky.Hypercohomology

/-!
# Base-field motivic cohomology from the literal reduced-cycle complex

The actual transfer-natural sheafification unit becomes a cochain isomorphism
after evaluation at the base field. Combining this with the genuine signed
shift and the proved unbounded derived-Hom bridge computes motivic cohomology
from the literal reduced-transfer singular complex.

The field is arbitrary. This is a structural evaluation theorem, with no
weight computation or change-of-ground-field claim.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe w u

namespace Motivic
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.SingularComplex

variable (k : Type u) [Field k]

/-- Literal reduced-transfer singular cochains evaluated at the base field,
with mathlib's genuine signed shift by `-q`, before any sheafification. -/
def motivicRawBaseComplex (q : ℕ) : CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  (((PresheafWithTransfers.toPresheaf k ⋙
    (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj
      (op (SmoothSite.base (Spec (.of k))))).mapHomologicalComplex (.up ℤ)).obj
        (PresheafWithTransfers.singularCochainComplex
          (PresheafWithTransfers.reducedTorus k q) 0))⟦-(q : ℤ)⟧

/-- Every occupied raw term is literally the reduced correspondence quotient
on the actual product of the base object and the algebraic simplex. -/
def motivicRawBaseComplexXIso (q r : ℕ) :
    (motivicRawBaseComplex k q).X (Indexing.singularDegree q r) ≅
      PresheafWithTransfers.sections (PresheafWithTransfers.reducedTorus k q)
        (Cor.simplexProduct (Cor.mk (SmoothSite.base (Spec (.of k)))) r) :=
  (PresheafWithTransfers.toPresheaf k ⋙
    (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj
      (op (SmoothSite.base (Spec (.of k))))).mapIso
        (PresheafWithTransfers.singularShiftedCochainXIso
          (PresheafWithTransfers.reducedTorus k q) q r)

/-- At the base field, the actual transfer-natural singular sheafification unit
is an isomorphism of the entire evaluated complex, including its differentials. -/
def motivicBaseSheafificationIso (q : ℕ) :
    ((PresheafWithTransfers.toPresheaf k ⋙
      (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj
        (op (SmoothSite.base (Spec (.of k))))).mapHomologicalComplex (.up ℤ)).obj
      (PresheafWithTransfers.singularCochainComplex
        (PresheafWithTransfers.reducedTorus k q) 0) ≅
    ((SheafWithTransfers.toSheaf k ⋙
      SmoothSite.nisnevichBaseEvaluation k).mapHomologicalComplex (.up ℤ)).obj
        (PresheafWithTransfers.singularSheafCochainComplex k
          (PresheafWithTransfers.reducedTorus k q) 0) := by
  let E := PresheafWithTransfers.toPresheaf k ⋙
    (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj
      (op (SmoothSite.base (Spec (.of k))))
  let f := (E.mapHomologicalComplex (.up ℤ)).map
    ((PresheafWithTransfers.singularSheafCochainUnit k 0).app
      (PresheafWithTransfers.reducedTorus k q))
  haveI (i : ℤ) : IsIso (f.f i) := by
    let P := (PresheafWithTransfers.singularCochainComplex
      (PresheafWithTransfers.reducedTorus k q) 0).X i
    change IsIso (((PresheafWithTransfers.toPresheaf k).map
      (PresheafWithTransfers.toNisnevichSheafify k P)).app
        (op (SmoothSite.base (Spec (.of k)))))
    rw [← PresheafWithTransfers.toSheafify_nisnevichSheafificationUnderlyingIso]
    let := SmoothSite.isIso_toSheafify_app_base k
      ((PresheafWithTransfers.toPresheaf k).obj P)
    change IsIso ((toSheafify _ _).app _ ≫
      (((PresheafWithTransfers.nisnevichSheafificationUnderlyingIso k).hom.app P).hom).app _)
    infer_instance
  haveI : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  let e := asIso f
  exact e

/-- The full literal signed reduced-cycle complex computes the actual base
sections of the canonical motivic sheaf complex. This is a cochain isomorphism. -/
def motivicRawBaseComplexIso (q : ℕ) : motivicRawBaseComplex k q ≅
    motivicBaseComplex k q :=
  (shiftFunctor (CochainComplex AddCommGrpCat.{u + 1} ℤ) (-(q : ℤ))).mapIso
      (motivicBaseSheafificationIso k q) ≪≫
    (((SheafWithTransfers.toSheaf k ⋙
      SmoothSite.nisnevichBaseEvaluation k).mapCochainComplexShiftIso (-(q : ℤ))).app
        (PresheafWithTransfers.singularSheafCochainComplex k
          (PresheafWithTransfers.reducedTorus k q) 0)).symm

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Genuine derived motivic cohomology at the base field is computed by the
literal shifted reduced-transfer singular complex, via the proved full cochain bridge. -/
def motivicRawBaseEvaluationComparison (p : ℤ) (q : ℕ) :
    motivicCohomology k p q (SmoothSite.base (Spec (.of k))) ≃+
      (motivicRawBaseComplex k q).homology p :=
  (motivicBaseEvaluationComparison k p q).trans
    (HomologicalComplex.homologyMapIso
      (motivicRawBaseComplexIso k q).symm p).addCommGroupIsoToAddEquiv

end Motivic
