/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.HypercohomologyEvaluationNaturality
public import Motivic.Cohomology.HypercohomologyFieldEvaluation
public import Motivic.Cohomology.Motivic.Indexing

/-! # The unbounded field-evaluation theorem preserves actual coefficient maps -/

@[expose] public noncomputable section

universe w u

open CategoryTheory AlgebraicGeometry Motivic.Hypercohomology

variable (J : GrothendieckTopology Scheme.{u})
  (hJ : J ≤ Motivic.Nisnevich.fieldLiftingTopology) (K : Type u) [Field K]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{u + 1})]

example {M N : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℤ}
    (f : M ⟶ N) (p : ℤ) (x : H.{w, u + 1, u, u + 1} J M p (Spec (.of K))) :
    fieldEvaluationComparison J hJ K N p
        (map.{w, u + 1, u, u + 1} J f p (Spec (.of K)) x) =
      HomologicalComplex.homologyMap
        (((Motivic.Nisnevich.fieldEvaluation J K).mapHomologicalComplex (.up ℤ)).map f) p
        (fieldEvaluationComparison J hJ K M p x) := by
  let := projective_freeAbelianSheaf_spec J hJ K
  exact evaluationComparison_naturality J (Spec (.of K)) f p x

section PlacedSingular

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{u})]

example (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ Sheaf J AddCommGrpCat.{u})
    (q : ℕ) (p : ℤ) (X : C) [Projective (freeAbelianSheaf J X)] :
    H J (Motivic.SingularComplex.cochainObj Δ P q) p X ≃+
      (evaluationComplex J X (Motivic.SingularComplex.cochainObj Δ P q)).homology p :=
  evaluationComparison J X (Motivic.SingularComplex.cochainObj Δ P q) p

end PlacedSingular
