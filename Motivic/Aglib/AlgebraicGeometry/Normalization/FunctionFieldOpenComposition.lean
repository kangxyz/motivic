/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.FiniteGenericallyEtaleField

/-! # The same function-field extension across the original compactifying open chart -/
@[expose] public noncomputable section
open CategoryTheory TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme

/-- Actual generic-point maps respect the unchanged composition of scheme morphisms. -/
theorem functionFieldSpecMap_comp
    {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant f] [IsDominant g] :
    Spec.map (CommRingCat.ofHom (functionFieldMap (f ≫ g))) =
      Spec.map (CommRingCat.ofHom (functionFieldMap f)) ≫
        Spec.map (CommRingCat.ofHom (functionFieldMap g)) := by
  apply (cancel_mono (Z.fromSpecStalk (genericPoint Z))).mp
  rw [← fromSpecStalk_genericPoint_naturality, Category.assoc,
    ← fromSpecStalk_genericPoint_naturality]
  calc
    X.fromSpecStalk (genericPoint X) ≫ f ≫ g =
        (X.fromSpecStalk (genericPoint X) ≫ f) ≫ g := (Category.assoc _ _ _).symm
    _ = (Spec.map (CommRingCat.ofHom (functionFieldMap f)) ≫
        Y.fromSpecStalk (genericPoint Y)) ≫ g :=
      congrArg (· ≫ g) (fromSpecStalk_genericPoint_naturality f)
    _ = _ := Category.assoc _ _ _

/-- An original dominant open chart induces an isomorphism of actual function fields. -/
theorem isIso_functionFieldSpecMap_of_isOpenImmersion
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (j : X ⟶ Y) [IsDominant j] [IsOpenImmersion j] :
    IsIso (Spec.map (CommRingCat.ofHom (functionFieldMap j))) := by
  have he := map_genericPoint_of_isDominant X j
  have hs : IsIso (Y.presheaf.stalkSpecializes (specializes_of_eq he)) := by
    generalize j (genericPoint X) = y at he ⊢
    subst y
    simp only [TopCat.Presheaf.stalkSpecializes_refl]
    infer_instance
  change IsIso (Spec.map (Y.presheaf.stalkSpecializes (specializes_of_eq he) ≫
    j.stalkMap (genericPoint X)))
  infer_instance

/-- Both properties needed by the finite normalization persist through the
same compactifying open immersion, without changing the coordinate functions. -/
theorem finite_etale_functionFieldSpecMap_comp_open
    {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (j : Y ⟶ Z) [IsDominant f] [IsDominant j] [IsOpenImmersion j]
    [IsFinite (Spec.map (CommRingCat.ofHom (functionFieldMap f)))]
    [Etale (Spec.map (CommRingCat.ofHom (functionFieldMap f)))] :
    IsFinite (Spec.map (CommRingCat.ofHom (functionFieldMap (f ≫ j)))) ∧
      Etale (Spec.map (CommRingCat.ofHom (functionFieldMap (f ≫ j)))) := by
  have := isIso_functionFieldSpecMap_of_isOpenImmersion j
  rw [functionFieldSpecMap_comp]
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
