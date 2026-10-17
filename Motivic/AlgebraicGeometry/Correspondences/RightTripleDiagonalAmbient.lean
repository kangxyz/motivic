/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleDiagonalIdeals
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

/-!
# Right-first incidence in the original six-factor ambient

The first support times the last two supports' actual incidence is the
Cartesian intersection of the second middle diagonal with the original
exterior coefficient support. A genuine pullback associator changes only
parentheses. The finite map used downstream remains the identity times the
last pair's scheme-image factor; no triple-to-right-pair finiteness is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g)
  (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The same right-first support, associated to match the original ambient. -/
abbrev rightIntermediateAssociatedSupport : Scheme.{u} :=
  pullback (F.supportProductTarget G) H.projection

/-- Only the original three support factors are reassociated, with both base
maps retained. No opposite or reversed correspondence is introduced. -/
def rightIntermediateSupportAssoc : F.rightIntermediateSupportProduct G H ≅
    F.rightIntermediateAssociatedSupport G H :=
  pullback.congrHom rfl (Category.assoc (G.incidenceFst H) G.projection g) ≪≫
    (pullbackAssoc (F.targetProjection ≫ g) (G.projection ≫ g)
      G.targetProjection H.projection).symm

/-- The associator retains the original first-support coordinate. -/
@[reassoc (attr := simp)] theorem rightIntermediateSupportAssoc_fst_fst :
    (F.rightIntermediateSupportAssoc G H).hom ≫
      pullback.fst (F.supportProductTarget G) H.projection ≫
        pullback.fst (F.targetProjection ≫ g) (G.projection ≫ g) =
    pullback.fst (F.targetProjection ≫ g) (G.incidenceSource H ≫ g) := by
  simp [rightIntermediateSupportAssoc, pullback.map, pullback.lift_fst]

/-- The associator retains the middle support of the original right incidence. -/
@[reassoc (attr := simp)] theorem rightIntermediateSupportAssoc_fst_snd :
    (F.rightIntermediateSupportAssoc G H).hom ≫
      pullback.fst (F.supportProductTarget G) H.projection ≫
        pullback.snd (F.targetProjection ≫ g) (G.projection ≫ g) =
    pullback.snd (F.targetProjection ≫ g) (G.incidenceSource H ≫ g) ≫ G.incidenceFst H := by
  simp [rightIntermediateSupportAssoc, pullback.map, incidenceFst, pullback.lift_snd_assoc]

/-- The associator retains the last support of the original right incidence. -/
@[reassoc (attr := simp)] theorem rightIntermediateSupportAssoc_snd :
    (F.rightIntermediateSupportAssoc G H).hom ≫
      pullback.snd (F.supportProductTarget G) H.projection =
    pullback.snd (F.targetProjection ≫ g) (G.incidenceSource H ≫ g) ≫ G.incidenceSnd H := by
  simp [rightIntermediateSupportAssoc, pullback.map, incidenceSnd, pullback.lift_snd_assoc]

/-- The associated right-first support embeds into the actual second diagonal. -/
def rightAssociatedSupportInclusion : F.rightIntermediateAssociatedSupport G H ⟶
    correspondenceSecondDiagonalAmbient f g h i :=
  pullback.map _ _ _ _ (F.supportProductInclusion G) H.inclusion (𝟙 Z)
    (by simp [supportProductTarget, correspondenceAmbientTarget, targetProjection])
    (by simp [projection, correspondenceProjection])

set_option backward.isDefEq.respectTransparency false in
instance : IsClosedImmersion (F.rightAssociatedSupportInclusion G H) := by
  unfold rightAssociatedSupportInclusion
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion (F.supportProductInclusion G)))
    (inferInstanceAs (IsClosedImmersion H.inclusion))
    (by simp [supportProductTarget, correspondenceAmbientTarget, targetProjection])
    (by simp [projection, correspondenceProjection])

/-- Forget only the imposed Z equality, keeping the original coefficient support. -/
abbrev rightAssociatedToTripleSupport : F.rightIntermediateAssociatedSupport G H ⟶
    F.tripleSupportProduct G H :=
  pullback.mapDesc (F.supportProductTarget G) H.projection h

/-- The associated support inclusion retains the exterior first two factors. -/
@[reassoc (attr := simp)] theorem rightAssociatedSupportInclusion_fst :
    F.rightAssociatedSupportInclusion G H ≫
      pullback.fst (correspondenceAmbientTarget f g h) (pullback.fst h i) =
    pullback.fst (F.supportProductTarget G) H.projection ≫ F.supportProductInclusion G :=
  pullback.lift_fst _ _ _

/-- The associated support inclusion retains the original last support. -/
@[reassoc (attr := simp)] theorem rightAssociatedSupportInclusion_snd :
    F.rightAssociatedSupportInclusion G H ≫
      pullback.snd (correspondenceAmbientTarget f g h) (pullback.fst h i) =
    pullback.snd (F.supportProductTarget G) H.projection ≫ H.inclusion :=
  pullback.lift_snd _ _ _

/-- Forgetting the Z equality preserves the first two original support factors. -/
@[reassoc (attr := simp)] theorem rightAssociatedToTripleSupport_fst :
    F.rightAssociatedToTripleSupport G H ≫
      pullback.fst (F.supportProductTarget G ≫ h) (H.projection ≫ h) =
    pullback.fst (F.supportProductTarget G) H.projection := by
  simp only [rightAssociatedToTripleSupport, pullback.mapDesc, pullback.map,
    pullback.lift_fst, Category.comp_id]

/-- Forgetting the Z equality preserves the original last support. -/
@[reassoc (attr := simp)] theorem rightAssociatedToTripleSupport_snd :
    F.rightAssociatedToTripleSupport G H ≫
      pullback.snd (F.supportProductTarget G ≫ h) (H.projection ≫ h) =
    pullback.snd (F.supportProductTarget G) H.projection := by
  simp only [rightAssociatedToTripleSupport, pullback.mapDesc, pullback.map,
    pullback.lift_snd, Category.comp_id]

/-- The associated support has the same original six-factor morphism by either route. -/
@[reassoc] theorem rightAssociated_ambient_comm :
    F.rightAssociatedSupportInclusion G H ≫ correspondenceSecondAmbientInclusion f g h i =
    F.rightAssociatedToTripleSupport G H ≫ F.tripleSupportProductInclusion G H := by
  apply pullback.hom_ext <;> simp

/-- The Z equality cuts out the genuine right-first support, in the parentheses
of the original six-factor ambient. -/
theorem rightAssociated_ambient_isPullback :
    IsPullback (F.rightAssociatedSupportInclusion G H) (F.rightAssociatedToTripleSupport G H)
      (correspondenceSecondAmbientInclusion f g h i) (F.tripleSupportProductInclusion G H) where
  w := F.rightAssociated_ambient_comm G H
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun c ↦ by
    have ha := congrArg (fun m => m ≫
      pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h)) c.condition
    have hb := congrArg (fun m => m ≫
      pullback.snd (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h)) c.condition
    simp only [Category.assoc, correspondenceSecondAmbientInclusion_fst,
      tripleSupportProductInclusion_fst] at ha
    simp only [Category.assoc, correspondenceSecondAmbientInclusion_snd,
      tripleSupportProductInclusion_snd] at hb
    have hbase :
        (c.snd ≫ pullback.fst (F.supportProductTarget G ≫ h) (H.projection ≫ h)) ≫
          F.supportProductTarget G =
        (c.snd ≫ pullback.snd (F.supportProductTarget G ≫ h) (H.projection ≫ h)) ≫
          H.projection := by
      calc
        _ = (c.snd ≫ pullback.fst _ _ ≫ F.supportProductInclusion G) ≫
            correspondenceAmbientTarget f g h := by
          simp [correspondenceAmbientTarget, supportProductTarget, targetProjection]
        _ = (c.fst ≫ pullback.fst _ _) ≫ correspondenceAmbientTarget f g h := by rw [ha]
        _ = (c.fst ≫ pullback.snd _ _) ≫ pullback.fst h i := by
          simp only [Category.assoc, pullback.condition]
        _ = _ := by rw [hb]; rfl
    let w : c.pt ⟶ F.rightIntermediateAssociatedSupport G H :=
      pullback.lift (c.snd ≫ pullback.fst _ _) (c.snd ≫ pullback.snd _ _) hbase
    have hw₁ : w ≫ F.rightAssociatedSupportInclusion G H = c.fst := by
      apply pullback.hom_ext
      · simpa only [Category.assoc, rightAssociatedSupportInclusion_fst,
          w, pullback.lift_fst_assoc] using ha.symm
      · simpa only [Category.assoc, rightAssociatedSupportInclusion_snd,
          w, pullback.lift_snd_assoc] using hb.symm
    have hw₂ : w ≫ F.rightAssociatedToTripleSupport G H = c.snd := by
      apply pullback.hom_ext
      · simp only [Category.assoc, w, pullback.lift_fst, Category.comp_id]
      · simp only [Category.assoc, w, pullback.lift_snd, Category.comp_id]
    refine ⟨w, hw₁, hw₂, ?_⟩
    intro m hm _
    exact (cancel_mono (F.rightAssociatedSupportInclusion G H)).mp (hm.trans hw₁.symm))⟩

/-- The genuine first-support-times-right-incidence embedding in the second diagonal. -/
def rightIntermediateSupportInclusion : F.rightIntermediateSupportProduct G H ⟶
    correspondenceSecondDiagonalAmbient f g h i :=
  (F.rightIntermediateSupportAssoc G H).hom ≫ F.rightAssociatedSupportInclusion G H

instance : IsClosedImmersion (F.rightIntermediateSupportInclusion G H) :=
  inferInstanceAs (IsClosedImmersion
    ((F.rightIntermediateSupportAssoc G H).hom ≫ F.rightAssociatedSupportInclusion G H))

/-- The genuine right-first support maps to the original exterior coefficient support. -/
def rightIntermediateToTripleSupport : F.rightIntermediateSupportProduct G H ⟶
    F.tripleSupportProduct G H :=
  (F.rightIntermediateSupportAssoc G H).hom ≫ F.rightAssociatedToTripleSupport G H

/-- The coefficient-support map retains the literal first-support coordinate. -/
@[reassoc (attr := simp)] theorem rightIntermediateToTripleSupport_fst_fst :
    F.rightIntermediateToTripleSupport G H ≫
      pullback.fst (F.supportProductTarget G ≫ h) (H.projection ≫ h) ≫
        pullback.fst (F.targetProjection ≫ g) (G.projection ≫ g) =
    pullback.fst (F.targetProjection ≫ g) (G.incidenceSource H ≫ g) := by
  simp [rightIntermediateToTripleSupport]

/-- The coefficient-support map retains the literal middle-support coordinate. -/
@[reassoc (attr := simp)] theorem rightIntermediateToTripleSupport_fst_snd :
    F.rightIntermediateToTripleSupport G H ≫
      pullback.fst (F.supportProductTarget G ≫ h) (H.projection ≫ h) ≫
        pullback.snd (F.targetProjection ≫ g) (G.projection ≫ g) =
    pullback.snd (F.targetProjection ≫ g) (G.incidenceSource H ≫ g) ≫ G.incidenceFst H := by
  simp [rightIntermediateToTripleSupport]

/-- The coefficient-support map retains the literal last-support coordinate. -/
@[reassoc (attr := simp)] theorem rightIntermediateToTripleSupport_snd :
    F.rightIntermediateToTripleSupport G H ≫
      pullback.snd (F.supportProductTarget G ≫ h) (H.projection ≫ h) =
    pullback.snd (F.targetProjection ≫ g) (G.incidenceSource H ≫ g) ≫ G.incidenceSnd H := by
  simp [rightIntermediateToTripleSupport]

/-- The right-first square retains exactly the same original six-factor map. -/
@[reassoc] theorem rightIntermediate_ambient_comm :
    F.rightIntermediateSupportInclusion G H ≫ correspondenceSecondAmbientInclusion f g h i =
    F.rightIntermediateToTripleSupport G H ≫ F.tripleSupportProductInclusion G H := by
  simp only [rightIntermediateSupportInclusion, rightIntermediateToTripleSupport,
    Category.assoc, rightAssociated_ambient_comm]

/-- The right-first Cartesian intersection is constructed, not assumed. It is
the original coefficient support intersected with the actual second diagonal. -/
theorem rightIntermediate_ambient_isPullback :
    IsPullback (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
      (correspondenceSecondAmbientInclusion f g h i) (F.tripleSupportProductInclusion G H) :=
  (F.rightAssociated_ambient_isPullback G H).of_iso
    (F.rightIntermediateSupportAssoc G H).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [rightIntermediateSupportInclusion])
    (by simp [rightIntermediateToTripleSupport]) (by simp) (by simp)

/-- The original ambient embedding of the genuine right-first support. -/
abbrev rightIntermediateAmbientInclusion : F.rightIntermediateSupportProduct G H ⟶
    correspondenceSixfoldAmbient f g h i :=
  F.rightIntermediateSupportInclusion G H ≫ correspondenceSecondAmbientInclusion f g h i

instance [IsSeparated h] : IsClosedImmersion (F.rightIntermediateAmbientInclusion G H) :=
  inferInstanceAs (IsClosedImmersion
    (F.rightIntermediateSupportInclusion G H ≫ correspondenceSecondAmbientInclusion f g h i))

/-- The right-first support ideal is literally the second-diagonal ideal plus
the original exterior coefficient ideal, without taking either reduction. -/
theorem ker_rightIntermediateAmbientInclusion [IsSeparated h] :
    (F.rightIntermediateAmbientInclusion G H).ker =
      (correspondenceSecondAmbientInclusion f g h i).ker ⊔
        (F.tripleSupportProductInclusion G H).ker :=
  ker_comp_eq_sup_of_isPullback _ _ _ _ (F.rightIntermediate_ambient_isPullback G H)

end Motivic.FiniteCorrespondenceGenerator
