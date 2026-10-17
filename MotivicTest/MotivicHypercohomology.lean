/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.Hypercohomology
public import Lean.Util.CollectAxioms

/-! # Genuine derived motivic cohomology and its exact base-field comparison -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Motivic

universe w u

namespace MotivicTest.MotivicHypercohomology

variable (k : Type u) [Field k]

example (q : ℕ) (i : ℤ) :
    (motivicSheafComplex k q).X i =
      (SheafWithTransfers.toSheaf k).obj ((motivicComplex k q).X i) := rfl

example (q : ℕ) (i j : ℤ) :
    (motivicSheafComplex k q).d i j =
      (SheafWithTransfers.toSheaf k).map ((motivicComplex k q).d i j) := rfl

example (q r : ℕ) :
    (motivicSheafComplex k q).X (Indexing.singularDegree q r) ≅
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).obj (motivicSingularPresheaf k q r) :=
  motivicSheafComplexXIso k q r

section ChosenDerivedCategory

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- This is definitionally the existing unbounded derived-Hom hypercohomology. -/
example (p : ℤ) (q : ℕ) (X : SmoothSite (Spec (.of k))) :
    motivicCohomology k p q X =
      Hypercohomology.H.{w, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) (motivicSheafComplex k q) p X := rfl

example (p : ℤ) (q : ℕ) (X : SmoothSite (Spec (.of k))) :
    AddCommGroup (motivicCohomology k p q X) := inferInstance

example (p : ℤ) (q : ℕ) (X : SmoothSite (Spec (.of k))) :
    motivicCohomologyRestriction k p q (𝟙 X) = 𝟙 _ :=
  (motivicCohomologyPresheaf k p q).map_id (op X)

example (p : ℤ) (q : ℕ) {X Y Z : SmoothSite (Spec (.of k))}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    motivicCohomologyRestriction k p q (f ≫ g) =
      motivicCohomologyRestriction k p q g ≫ motivicCohomologyRestriction k p q f :=
  (motivicCohomologyPresheaf k p q).map_comp g.op f.op

/-- All integer degrees are allowed; no bounded-below restriction is inserted. -/
def everyDegree (p : ℤ) (q : ℕ) :
    motivicCohomology k p q (SmoothSite.base (Spec (.of k))) ≃+
      (motivicBaseComplex k q).homology p :=
  motivicBaseEvaluationComparison k p q

end ChosenDerivedCategory

/-- A real consumer uses the standard large derived category, with no smallness assumption. -/
def standardLargeFieldComparison (p : ℤ) (q : ℕ) :=
  letI := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  motivicBaseEvaluationComparison k p q

/-- Negative degrees in weight two are covered by the same genuine derived bridge. -/
def negativeDegreeComparison := standardLargeFieldComparison k (-4) 2

open Lean in
run_cmd do
  for name in #[``motivicSheafComplex, ``motivicSheafComplex_X, ``motivicSheafComplex_d,
      ``motivicSheafComplexXIso, ``motivicBaseComplex, ``motivicBaseComplex_X,
      ``motivicBaseComplex_d, ``motivicCohomology, ``motivicCohomologyPresheaf,
      ``motivicCohomologyPresheaf_obj, ``motivicCohomologyRestriction,
      ``motivicBaseEvaluationComparison, ``everyDegree, ``standardLargeFieldComparison,
      ``negativeDegreeComparison] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Motivic hypercohomology and field evaluation use only standard Lean foundations."

end MotivicTest.MotivicHypercohomology
