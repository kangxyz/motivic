/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.SmoothSlice
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.CohomologySource
public import Mathlib.Algebra.Category.Grp.AB

/-! Exactness of the genuine left adjoint to big-to-small restriction. -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {B : Scheme.{u}} [IsAffine B] (X : SmoothSite B)

/-- Pointwise Kan extension on the actual unequal-universe site categories. -/
def sliceLanEvaluationIso (V : (Over X)ᵒᵖ) :
    (toSmoothSlice X).op.lan ⋙ (CategoryTheory.evaluation (Over X)ᵒᵖ AddCommGrpCat.{u + 1}).obj V ≅
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
        (CostructuredArrow.proj (toSmoothSlice X).op V) ⋙ colim :=
  NatIso.ofComponents (fun P =>
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit (toSmoothSlice X).op P V)
      (colimit.isColimit _)) (fun {P Q} φ => by
        apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
          (toSmoothSlice X).op P V).hom_ext
        intro T
        have h₁ := fun (P : (EtaleSeparatedFiniteType X.left)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) =>
          IsColimit.comp_coconePointUniqueUpToIso_hom
            (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
              (toSmoothSlice X).op P V) (colimit.isColimit _) T
        have h₂ := congr_app ((toSmoothSlice X).op.lanUnit.naturality φ) T.left
        dsimp at h₁ h₂ ⊢
        simp only [Category.assoc] at h₁ ⊢
        simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
        rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
          ι_colimMap, Functor.whiskerLeft_app]
        rfl)

instance sliceLan_preservesFiniteLimits :
    PreservesFiniteLimits
      ((toSmoothSlice X).op.lan : _ ⥤ (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) := by
  let : AB5OfSize.{u, u + 1} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} _
  apply preservesFiniteLimits_of_evaluation
  intro V
  have : IsFiltered (CostructuredArrow (toSmoothSlice X).op V) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (toSmoothSlice X) V.unop)
  exact preservesFiniteLimits_of_natIso (sliceLanEvaluationIso X V).symm

instance slicePullback_preservesFiniteLimits :
    PreservesFiniteLimits ((toSmoothSlice X).sheafPullback AddCommGrpCat.{u + 1}
      (nisnevichTopology X.left) ((SmoothSite.nisnevichTopology B).over X)) :=
  Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

/-- Factor extension through the actual smooth slice. -/
def factoredExtend : Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1} ⥤
    Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1} :=
  (toSmoothSlice X).sheafPullback _ _ _ ⋙
    SliceSheaf.extension (SmoothSite.nisnevichTopology B) X AddCommGrpCat.{u + 1}

/-- The factored left adjoint has exactly the original restriction as right adjoint. -/
def factoredExtendAdjunction : factoredExtend X ⊣ restrict X AddCommGrpCat.{u + 1} :=
  (((toSmoothSlice X).sheafAdjunctionContinuous _ _ _).comp
    (SliceSheaf.adjunction (SmoothSite.nisnevichTopology B) X AddCommGrpCat.{u + 1})).ofNatIsoRight
      (NatIso.ofComponents (fun F => Iso.refl _) (by intros; rfl))

/-- The factorization identifies the native original left adjoint, without replacing it. -/
def extendFactorizationIso : extend X ≅ factoredExtend X :=
  (extendRestrictAdjunction X).leftAdjointUniq (factoredExtendAdjunction X)

instance : PreservesFiniteLimits (factoredExtend X) := by
  let : AB4OfSize.{u} AddCommGrpCat.{u + 1} := AB4OfSize_shrink.{u, u + 1} _
  unfold factoredExtend
  infer_instance

instance : PreservesFiniteLimits (extend X) :=
  preservesFiniteLimits_of_natIso (extendFactorizationIso X).symm

instance : (extend X).IsLeftAdjoint := (extendRestrictAdjunction X).isLeftAdjoint

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
