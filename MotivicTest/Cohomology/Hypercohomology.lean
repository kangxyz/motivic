/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.Hypercohomology.SheafComparison
public import Motivic.Aglib.AlgebraicGeometry.Sites.Hypercohomology.FieldEvaluation

/-!
# Consumers of unbounded ordinary-sheaf hypercohomology

These tests check actual coefficient maps and restrictions, quasi-isomorphism
invariance, the degree-zero sheaf comparison and the evaluated-complex
comparison. The target complex is arbitrary; no bounded-below instance is used.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory Opposite _root_.CategoryTheory.Sheaf.Hypercohomology

section LargeSite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v}]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{max u v})]
  (K L M : CochainComplex (Sheaf J AddCommGrpCat.{max u v}) ℤ)
  (p : ℤ) (X Y : C)

example (f : K ⟶ L) (g : L ⟶ M) (x : H J K p X) :
    map J (f ≫ g) p X x = map J g p X (map J f p X x) := by
  rw [map_comp]
  rfl

example (f : K ⟶ L) [QuasiIso f] :
    IsIso ((presheafFunctor J p).map f) := inferInstance

example (f : X ⟶ Y) (x : H J K p Y) :
    restriction J K p f x =
      (DerivedCategory.singleFunctor _ 0).map ((freeAbelianSheafFunctor J).map f) ≫ x :=
  restriction_apply J K p f x

example [Projective (freeAbelianSheaf J X)] :
    H J K p X ≃+ (evaluationComplex J X K).homology p :=
  evaluationComparison J X K p

end LargeSite

section OrdinarySheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{v})]
  (F : Sheaf J AddCommGrpCat.{v}) (X : C)

example : H J ((CochainComplex.singleFunctor _ 0).obj F) 0 X ≃+ F.obj.obj (op X) :=
  singleZeroSections J F X

example [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] (n : ℕ) :
    H J ((CochainComplex.singleFunctor _ 0).obj F) (n : ℤ) X ≃+ F.H' n X :=
  singleComparison J F n X

end OrdinarySheaf

section StandardLocalization

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v}]

/-- An actual complex with the same sheaf in every integer degree and zero differentials. -/
def zeroDifferentialComplex (F : Sheaf J AddCommGrpCat.{max u v}) :
    CochainComplex (Sheaf J AddCommGrpCat.{max u v}) ℤ where
  X _ := F
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

attribute [local instance] HasDerivedCategory.standard in
example (F : Sheaf J AddCommGrpCat.{max u v}) (X : C) :
    AddCommGroup (H J (zeroDifferentialComplex J F) (-3) X) := inferInstance

end StandardLocalization

section Field

open AlgebraicGeometry

variable (J : GrothendieckTopology Scheme.{u})
  (hJ : J ≤ Nisnevich.fieldLiftingTopology) (K : Type u) [Field K]

include hJ

attribute [local instance] HasDerivedCategory.standard in
example (M : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℤ) (p : ℤ) :
    H.{_, u + 1, u, u + 1} J M p (Spec (.of K)) ≃+
      (((Nisnevich.fieldEvaluation J K).mapHomologicalComplex (.up ℤ)).obj M).homology
        p :=
  fieldEvaluationComparison J hJ K M p

end Field
