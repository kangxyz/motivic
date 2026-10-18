/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.RestrictionSourceNaturality
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Composition coherence for the original free sheaf sources

The comparison is the actual uniqueness isomorphism of continuous-site
adjunctions. The equation retains the given site-functor comparison and is
proved by the original section-representing equivalences.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
universe t v u u' u''
namespace Motivic.Hypercohomology
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
  {E : Type u''} [Category.{v} E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (L : GrothendieckTopology E)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasSheafify K AddCommGrpCat.{max v t}]
  [HasSheafify L AddCommGrpCat.{max v t}]
  (G : C ⥤ D) (H : D ⥤ E) [G.IsContinuous J K] [H.IsContinuous K L]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max v t} J K).IsRightAdjoint]
  [(H.sheafPushforwardContinuous AddCommGrpCat.{max v t} K L).IsRightAdjoint]

/-- Iterated source comparisons preserve the original represented section. -/
theorem restrictionSourceIso_comp_sections (X : C)
    (F : Sheaf L AddCommGrpCat.{max v t})
    (f : freeAbelianSheaf L (H.obj (G.obj X)) ⟶ F) :
    sectionsEquiv J X _
      (((G.sheafAdjunctionContinuous AddCommGrpCat J K).comp
        (H.sheafAdjunctionContinuous AddCommGrpCat K L)).homEquiv _ _
        ((H.sheafPullback AddCommGrpCat K L).map (restrictionSourceIso J K G X).hom ≫
          (restrictionSourceIso K L H (G.obj X)).hom ≫ f)) =
      sectionsEquiv L (H.obj (G.obj X)) F f := by
  change sectionsEquiv J X _
    ((G.sheafAdjunctionContinuous AddCommGrpCat J K).homEquiv _ _
      ((H.sheafAdjunctionContinuous AddCommGrpCat K L).homEquiv _ _
        ((H.sheafPullback AddCommGrpCat K L).map (restrictionSourceIso J K G X).hom ≫
          (restrictionSourceIso K L H (G.obj X)).hom ≫ f))) = _
  have he := Adjunction.homEquiv_naturality_left
    (H.sheafAdjunctionContinuous AddCommGrpCat K L)
    (restrictionSourceIso J K G X).hom ((restrictionSourceIso K L H (G.obj X)).hom ≫ f)
  exact (congrArg (fun z => sectionsEquiv J X _
    ((G.sheafAdjunctionContinuous AddCommGrpCat J K).homEquiv _ _ z)) he).trans
      ((restrictionSourceIso_sections J K G X _ _).trans
        (restrictionSourceIso_sections K L H (G.obj X) F f))

variable (T : C ⥤ E) [T.IsContinuous J L]
  [(T.sheafPushforwardContinuous AddCommGrpCat.{max v t} J L).IsRightAdjoint]
  (e : G ⋙ H ≅ T)

/-- Actual composition comparison induced by the original pushforward comparison. -/
def restrictionPullbackCompIso :
    G.sheafPullback AddCommGrpCat.{max v t} J K ⋙
      H.sheafPullback AddCommGrpCat K L ≅ T.sheafPullback AddCommGrpCat J L :=
  (((G.sheafAdjunctionContinuous AddCommGrpCat J K).comp
    (H.sheafAdjunctionContinuous AddCommGrpCat K L)).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp' e AddCommGrpCat J K L)).leftAdjointUniq
        (T.sheafAdjunctionContinuous AddCommGrpCat J L)

/-- Composition of the actual source isomorphisms agrees with the actual
inverse-image composition isomorphism and the given site comparison. -/
theorem restrictionSourceIso_comp (X : C) :
    (H.sheafPullback AddCommGrpCat.{max v t} K L).map
        (restrictionSourceIso J K G X).hom ≫
      (restrictionSourceIso K L H (G.obj X)).hom ≫
        (freeAbelianSheafFunctor L).map (e.hom.app X) =
      (restrictionPullbackCompIso J K L G H T e).hom.app (freeAbelianSheaf J X) ≫
        (restrictionSourceIso J L T X).hom := by
  let adj := ((G.sheafAdjunctionContinuous AddCommGrpCat J K).comp
    (H.sheafAdjunctionContinuous AddCommGrpCat K L)).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp' e AddCommGrpCat J K L)
  apply (adj.homEquiv _ _).injective
  apply (sectionsEquiv J X _).injective
  have hright : sectionsEquiv J X _
      (adj.homEquiv _ _
        ((restrictionPullbackCompIso J K L G H T e).hom.app (freeAbelianSheaf J X) ≫
          (restrictionSourceIso J L T X).hom)) =
      sectionsEquiv L (T.obj X) _ (𝟙 (freeAbelianSheaf L (T.obj X))) := by
    have ha : adj.homEquiv _ _
        ((restrictionPullbackCompIso J K L G H T e).hom.app (freeAbelianSheaf J X)) =
        (T.sheafAdjunctionContinuous AddCommGrpCat J L).unit.app (freeAbelianSheaf J X) :=
      Adjunction.homEquiv_leftAdjointUniq_hom_app adj
        (T.sheafAdjunctionContinuous AddCommGrpCat J L) _
    have hr : adj.homEquiv _ _
        ((restrictionPullbackCompIso J K L G H T e).hom.app (freeAbelianSheaf J X) ≫
          (restrictionSourceIso J L T X).hom) = restrictionSourceHom J L T X :=
      (Adjunction.homEquiv_naturality_right adj _ _).trans
        (congrArg (fun z => z ≫ (T.sheafPushforwardContinuous AddCommGrpCat J L).map
          (restrictionSourceIso J L T X).hom) ha)
    exact (congrArg (sectionsEquiv J X _) hr).trans (restrictionSourceHom_sections J L T X)
  rw [hright]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, sectionsEquiv_naturality]
  change (freeAbelianSheaf L (T.obj X)).obj.map (e.inv.app X).op
      (sectionsEquiv J X _
        (((G.sheafAdjunctionContinuous AddCommGrpCat J K).comp
          (H.sheafAdjunctionContinuous AddCommGrpCat K L)).homEquiv _ _
          ((H.sheafPullback AddCommGrpCat K L).map
              (restrictionSourceIso J K G X).hom ≫
            (restrictionSourceIso K L H (G.obj X)).hom ≫
              (freeAbelianSheafFunctor L).map (e.hom.app X)))) = _
  rw [restrictionSourceIso_comp_sections]
  exact (sectionsEquiv_restriction L (e.inv.app X) _
    ((freeAbelianSheafFunctor L).map (e.hom.app X))).symm.trans
      (congrArg (sectionsEquiv L (T.obj X) _)
        (((freeAbelianSheafFunctor L).mapIso (e.app X)).inv_hom_id))

end Motivic.Hypercohomology
