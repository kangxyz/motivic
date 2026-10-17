/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafCohomologyRestrictionSource
public import Motivic.Aglib.CategoryTheory.Sites.FreeAbelianSheafPushout

/-! # Naturality of the original free sources for site restriction -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite
universe t v u u'
namespace Motivic.Hypercohomology
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasSheafify K AddCommGrpCat.{max v t}]
  (G : C ⥤ D) [G.IsContinuous J K]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max v t} J K).IsRightAdjoint]

/-- The canonical source map adjoint to the actual free-source isomorphism. -/
def restrictionSourceHom (X : C) : freeAbelianSheaf J X ⟶
    (G.sheafPushforwardContinuous AddCommGrpCat J K).obj (freeAbelianSheaf K (G.obj X)) :=
  (G.sheafAdjunctionContinuous AddCommGrpCat J K).homEquiv _ _
    (restrictionSourceIso J K G X).hom

/-- The canonical isomorphism intertwines the original section-representing equivalences. -/
theorem restrictionSourceIso_sections (X : C) (F : Sheaf K AddCommGrpCat.{max v t})
    (f : freeAbelianSheaf K (G.obj X) ⟶ F) :
    sectionsEquiv J X _
      ((G.sheafAdjunctionContinuous AddCommGrpCat J K).homEquiv _ _
        ((restrictionSourceIso J K G X).hom ≫ f)) = sectionsEquiv K (G.obj X) F f := by
  change (restrictedSectionsCorepresentable J K G X).homEquiv
    (((restrictedSectionsCorepresentable J K G X).uniqueUpToIso
      (sectionsCorepresentable K (G.obj X))).hom ≫ f) = _
  change (restrictedSectionsCorepresentable J K G X).homEquiv
    ((restrictedSectionsCorepresentable J K G X).homEquiv.symm
      ((sectionsCorepresentable K (G.obj X)).homEquiv (𝟙 _)) ≫ f) = _
  rw [Functor.CorepresentableBy.homEquiv_comp, Equiv.apply_symm_apply]
  exact ((sectionsCorepresentable K (G.obj X)).homEquiv_comp f (𝟙 _)).symm.trans
    (by simp only [Category.id_comp]; rfl)

/-- The canonical source map is the literal identity section under both representations. -/
theorem restrictionSourceHom_sections (X : C) :
    sectionsEquiv J X _ (restrictionSourceHom J K G X) =
      sectionsEquiv K (G.obj X) _ (𝟙 (freeAbelianSheaf K (G.obj X))) := by
  simpa only [Category.comp_id, restrictionSourceHom] using restrictionSourceIso_sections J K G X _
    (𝟙 (freeAbelianSheaf K (G.obj X)))

/-- The original free-source map is natural in the site object. -/
theorem restrictionSourceHom_naturality {X Y : C} (f : X ⟶ Y) :
    (freeAbelianSheafFunctor J).map f ≫ restrictionSourceHom J K G Y =
      restrictionSourceHom J K G X ≫
        (G.sheafPushforwardContinuous AddCommGrpCat J K).map
          ((freeAbelianSheafFunctor K).map (G.map f)) := by
  apply (sectionsEquiv J X _).injective
  rw [sectionsEquiv_restriction, restrictionSourceHom_sections,
    sectionsEquiv_naturality, restrictionSourceHom_sections]
  change _ = ((freeAbelianSheafFunctor K).map (G.map f)).hom.app _
    (sectionsEquiv K (G.obj X) _ (𝟙 _))
  rw [← sectionsEquiv_naturality, Category.id_comp,
    ← Category.comp_id ((freeAbelianSheafFunctor K).map (G.map f)),
    sectionsEquiv_restriction]
  rfl

/-- The actual free-source isomorphism is natural, not merely an objectwise identification. -/
theorem restrictionSourceIso_naturality {X Y : C} (f : X ⟶ Y) :
    (G.sheafPullback AddCommGrpCat J K).map ((freeAbelianSheafFunctor J).map f) ≫
        (restrictionSourceIso J K G Y).hom =
      (restrictionSourceIso J K G X).hom ≫
        (freeAbelianSheafFunctor K).map (G.map f) := by
  apply ((G.sheafAdjunctionContinuous AddCommGrpCat J K).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  exact restrictionSourceHom_naturality J K G f

end Motivic.Hypercohomology
