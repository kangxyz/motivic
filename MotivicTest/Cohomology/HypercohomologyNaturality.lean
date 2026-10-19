/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.Hypercohomology.EvaluationNaturality
public import Motivic.Aglib.AlgebraicGeometry.Sites.Hypercohomology.FieldEvaluation
public import Motivic.Aglib.Algebra.Homology.SingularComplex.Indexing

/-! # The unbounded field-evaluation theorem preserves actual coefficient maps -/

@[expose] public noncomputable section

universe w u

open CategoryTheory AlgebraicGeometry _root_.CategoryTheory.Sheaf.Hypercohomology

variable (J : GrothendieckTopology Scheme.{u})
  (hJ : J ≤ Nisnevich.fieldLiftingTopology) (K : Type u) [Field K]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{u + 1})]

example {M N : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℤ}
    (f : M ⟶ N) (p : ℤ) (x : H.{w, u + 1, u, u + 1} J M p (Spec (.of K))) :
    fieldEvaluationComparison J hJ K N p
        (map.{w, u + 1, u, u + 1} J f p (Spec (.of K)) x) =
      HomologicalComplex.homologyMap
        (((Nisnevich.fieldEvaluation J K).mapHomologicalComplex (.up ℤ)).map f) p
        (fieldEvaluationComparison J hJ K M p x) := by
  let := projective_freeAbelianSheaf_spec J hJ K
  exact evaluationComparison_naturality J (Spec (.of K)) f p x

section PlacedSingular

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{u})]

example (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ Sheaf J AddCommGrpCat.{u})
    (q : ℕ) (p : ℤ) (X : C) [Projective (freeAbelianSheaf J X)] :
    H J (SingularComplex.cochainObj Δ P q) p X ≃+
      (evaluationComplex J X (SingularComplex.cochainObj Δ P q)).homology p :=
  evaluationComparison J X (SingularComplex.cochainObj Δ P q) p

end PlacedSingular
