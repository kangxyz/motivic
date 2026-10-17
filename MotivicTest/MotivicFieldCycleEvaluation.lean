/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.FieldCycleEvaluation
public import Lean.Util.CollectAxioms

/-! # Exact evaluation by the full literal signed reduced-cycle complex -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Motivic

universe w u

namespace MotivicTest.MotivicFieldCycleEvaluation

variable (k : Type u) [Field k]

/-- Before sheafification, the evaluated coefficient is shifted by the actual `-q` functor. -/
example (q : ℕ) : motivicRawBaseComplex k q =
    (((PresheafWithTransfers.toPresheaf k ⋙
      (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj
        (op (SmoothSite.base (Spec (.of k))))).mapHomologicalComplex (.up ℤ)).obj
          (PresheafWithTransfers.singularCochainComplex
            (PresheafWithTransfers.reducedTorus k q) 0))⟦-(q : ℤ)⟧ := rfl

/-- Literal products remain visible after every arbitrary-degree placement. -/
example (q r : ℕ) :
    (motivicRawBaseComplex k q).X (Indexing.singularDegree q r) ≅
      PresheafWithTransfers.sections (PresheafWithTransfers.reducedTorus k q)
        (Cor.simplexProduct (Cor.mk (SmoothSite.base (Spec (.of k)))) r) :=
  motivicRawBaseComplexXIso k q r

example (q : ℕ) : motivicRawBaseComplex k q ≅ motivicBaseComplex k q :=
  motivicRawBaseComplexIso k q

/-- The bridge is compatible with all differentials, not just termwise bijections. -/
example (q : ℕ) (i j : ℤ) :
    (motivicRawBaseComplexIso k q).hom.f i ≫ (motivicBaseComplex k q).d i j =
      (motivicRawBaseComplex k q).d i j ≫ (motivicRawBaseComplexIso k q).hom.f j :=
  (motivicRawBaseComplexIso k q).hom.comm i j

section ChosenDerivedCategory

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Actual derived motivic cohomology is computed by the literal raw complex. -/
def everyDegree (p : ℤ) (q : ℕ) :
    motivicCohomology k p q (SmoothSite.base (Spec (.of k))) ≃+
      (motivicRawBaseComplex k q).homology p :=
  motivicRawBaseEvaluationComparison k p q

end ChosenDerivedCategory

/-- The full cycle bridge has a consumer with the standard large derived category. -/
def standardLargeCycleComparison (p : ℤ) (q : ℕ) :=
  letI := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  motivicRawBaseEvaluationComparison k p q

open Lean in
run_cmd do
  for name in #[``motivicRawBaseComplex, ``motivicRawBaseComplexXIso,
      ``motivicBaseSheafificationIso,
      ``motivicRawBaseComplexIso, ``motivicRawBaseEvaluationComparison,
      ``everyDegree, ``standardLargeCycleComparison] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "The full motivic cycle-evaluation bridge uses only standard Lean foundations."

end MotivicTest.MotivicFieldCycleEvaluation
