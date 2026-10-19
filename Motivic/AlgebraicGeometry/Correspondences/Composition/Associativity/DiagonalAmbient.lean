/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Products.Diagonal.TripleAmbient

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.IncidenceSupport
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Intersection.AmbientIdeal

/-!
# Actual six-factor and successive-diagonal support geometry

The exterior product of three genuine supports lies in the six-factor ambient
scheme. The first middle diagonal cuts out the pair incidence times the last
support, and the second cuts out the full triple incidence. All maps and
Cartesian squares retain the original scheme structures and their nilpotents.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme.Hom _root_.AlgebraicGeometry.Scheme.Products

variable {f g h i}
  (F : FiniteCorrespondenceGenerator f g)
  (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The last coordinate of the actual first two support factors. -/
abbrev supportProductTarget : F.supportProduct G ⟶ Z :=
  pullback.snd (F.targetProjection ≫ g) (G.projection ≫ g) ≫ G.targetProjection

/-- The genuine exterior product of all three support schemes. -/
abbrev tripleSupportProduct : Scheme.{u} :=
  pullback (F.supportProductTarget G ≫ h) (H.projection ≫ h)

/-- The actual exterior support inclusion into the six-factor ambient. -/
def tripleSupportProductInclusion : F.tripleSupportProduct G H ⟶
    correspondenceSixfoldAmbient f g h i :=
  pullback.map _ _ _ _ (F.supportProductInclusion G) H.inclusion (𝟙 S)
    (by simp [supportProductTarget, correspondenceAmbientTarget, targetProjection])
    (by simp [projection, correspondenceProjection])

set_option backward.isDefEq.respectTransparency false in
instance : IsClosedImmersion (F.tripleSupportProductInclusion G H) := by
  unfold tripleSupportProductInclusion
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion (F.supportProductInclusion G)))
    (inferInstanceAs (IsClosedImmersion H.inclusion)) (by simp)
    (by simp [projection, correspondenceProjection])

/-- The genuine first-stage support embeds in the first-diagonal ambient. -/
def leftIntermediateSupportInclusion : F.leftIntermediateSupportProduct G H ⟶
    correspondenceFirstDiagonal f g h i :=
  pullback.map _ _ _ _ (F.incidenceInclusion G) H.inclusion (𝟙 S)
    (by simp [incidenceTarget, correspondenceTripleTarget])
    (by simp [projection, correspondenceProjection])

set_option backward.isDefEq.respectTransparency false in
instance : IsClosedImmersion (F.leftIntermediateSupportInclusion G H) := by
  unfold leftIntermediateSupportInclusion
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion (F.incidenceInclusion G)))
    (inferInstanceAs (IsClosedImmersion H.inclusion)) (by simp)
    (by simp [projection, correspondenceProjection])

/-- First-stage support maps to the original exterior coefficient support. -/
def leftIntermediateToTripleSupport : F.leftIntermediateSupportProduct G H ⟶
    F.tripleSupportProduct G H :=
  pullback.map _ _ _ _ (F.incidenceToSupportProduct G) (𝟙 H.scheme) (𝟙 S)
    (by simp [incidenceTarget, supportProductTarget]) (by simp)

/-- Exterior support inclusion on its first pair. -/
@[reassoc (attr := simp)] theorem tripleSupportProductInclusion_fst :
    F.tripleSupportProductInclusion G H ≫
      pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.fst (F.supportProductTarget G ≫ h) (H.projection ≫ h) ≫
      F.supportProductInclusion G := pullback.lift_fst _ _ _

/-- Exterior support inclusion on its last support. -/
@[reassoc (attr := simp)] theorem tripleSupportProductInclusion_snd :
    F.tripleSupportProductInclusion G H ≫
      pullback.snd (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.snd (F.supportProductTarget G ≫ h) (H.projection ≫ h) ≫ H.inclusion :=
  pullback.lift_snd _ _ _

/-- First-stage support inclusion on its incidence factor. -/
@[reassoc (attr := simp)] theorem leftIntermediateSupportInclusion_fst :
    F.leftIntermediateSupportInclusion G H ≫
      pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.fst (F.incidenceTarget G ≫ h) (H.projection ≫ h) ≫ F.incidenceInclusion G :=
  pullback.lift_fst _ _ _

/-- First-stage support inclusion on its last support. -/
@[reassoc (attr := simp)] theorem leftIntermediateSupportInclusion_snd :
    F.leftIntermediateSupportInclusion G H ≫
      pullback.snd (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.snd (F.incidenceTarget G ≫ h) (H.projection ≫ h) ≫ H.inclusion :=
  pullback.lift_snd _ _ _

/-- The map to the coefficient support keeps the actual pair-to-product map. -/
@[reassoc (attr := simp)] theorem leftIntermediateToTripleSupport_fst :
    F.leftIntermediateToTripleSupport G H ≫
      pullback.fst (F.supportProductTarget G ≫ h) (H.projection ≫ h) =
    pullback.fst (F.incidenceTarget G ≫ h) (H.projection ≫ h) ≫
      F.incidenceToSupportProduct G := pullback.lift_fst _ _ _

/-- The map to the coefficient support keeps the third support unchanged. -/
@[reassoc (attr := simp)] theorem leftIntermediateToTripleSupport_snd :
    F.leftIntermediateToTripleSupport G H ≫
      pullback.snd (F.supportProductTarget G ≫ h) (H.projection ≫ h) =
    pullback.snd (F.incidenceTarget G ≫ h) (H.projection ≫ h) := by
  simp only [leftIntermediateToTripleSupport, pullback.map, pullback.lift_snd,
    Category.comp_id]

/-- Both first-stage maps give the same actual six-factor ambient morphism. -/
@[reassoc] theorem leftIntermediate_ambient_comm :
    F.leftIntermediateSupportInclusion G H ≫ correspondenceFirstDiagonalInclusion f g h i =
    F.leftIntermediateToTripleSupport G H ≫ F.tripleSupportProductInclusion G H := by
  apply pullback.hom_ext
  · simp only [Category.assoc, correspondenceFirstDiagonalInclusion_fst,
      leftIntermediateSupportInclusion_fst_assoc, tripleSupportProductInclusion_fst,
      leftIntermediateToTripleSupport_fst_assoc, incidence_ambient_comm]
  · simp

/-- The first diagonal and the exterior coefficient support have exactly the
actual pair-incidence-times-third-support scheme as Cartesian intersection. -/
theorem leftIntermediate_ambient_isPullback :
    IsPullback (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
      (correspondenceFirstDiagonalInclusion f g h i) (F.tripleSupportProductInclusion G H) where
  w := F.leftIntermediate_ambient_comm G H
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun c ↦ by
    have ha := congrArg (fun m => m ≫
      pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h)) c.condition
    have hb := congrArg (fun m => m ≫
      pullback.snd (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h)) c.condition
    simp only [Category.assoc, correspondenceFirstDiagonalInclusion_fst,
      tripleSupportProductInclusion_fst] at ha
    simp only [Category.assoc, correspondenceFirstDiagonalInclusion_snd,
      tripleSupportProductInclusion_snd] at hb
    let v : c.pt ⟶ F.incidence G := (F.incidence_ambient_isPullback G).lift
      (c.fst ≫ pullback.fst _ _) (c.snd ≫ pullback.fst _ _) (by
        simpa only [Category.assoc] using ha)
    have hv₁ : v ≫ F.incidenceInclusion G = c.fst ≫ pullback.fst _ _ :=
      IsPullback.lift_fst _ _ _ _
    have hv₂ : v ≫ F.incidenceToSupportProduct G = c.snd ≫ pullback.fst _ _ :=
      IsPullback.lift_snd _ _ _ _
    have hbase : v ≫ (F.incidenceTarget G ≫ h) =
        (c.snd ≫ pullback.snd (F.supportProductTarget G ≫ h) (H.projection ≫ h)) ≫
          (H.projection ≫ h) := by
      calc
        _ = (v ≫ F.incidenceToSupportProduct G) ≫ (F.supportProductTarget G ≫ h) := by
          simp [supportProductTarget, incidenceTarget]
        _ = (c.snd ≫ pullback.fst _ _) ≫ (F.supportProductTarget G ≫ h) := by rw [hv₂]
        _ = _ := by
          simpa only [Category.assoc] using congrArg (c.snd ≫ ·)
            (pullback.condition (f := F.supportProductTarget G ≫ h) (g := H.projection ≫ h))
    let w : c.pt ⟶ F.leftIntermediateSupportProduct G H :=
      pullback.lift v (c.snd ≫ pullback.snd _ _) hbase
    have hw₁ : w ≫ F.leftIntermediateSupportInclusion G H = c.fst := by
      apply pullback.hom_ext
      · simpa only [Category.assoc, leftIntermediateSupportInclusion_fst,
          w, pullback.lift_fst_assoc] using hv₁
      · simpa only [Category.assoc, leftIntermediateSupportInclusion_snd,
          w, pullback.lift_snd_assoc] using hb.symm
    have hw₂ : w ≫ F.leftIntermediateToTripleSupport G H = c.snd := by
      apply pullback.hom_ext
      · simpa only [Category.assoc, leftIntermediateToTripleSupport_fst,
          w, pullback.lift_fst_assoc] using hv₂
      · simp only [Category.assoc, leftIntermediateToTripleSupport_snd,
          w, pullback.lift_snd]
    refine ⟨w, hw₁, hw₂, ?_⟩
    intro m hm _
    exact (cancel_mono (F.leftIntermediateSupportInclusion G H)).mp (hm.trans hw₁.symm))⟩

/-- The first-stage ambient map keeps the entire original scheme structure. -/
abbrev leftIntermediateAmbientInclusion : F.leftIntermediateSupportProduct G H ⟶
    correspondenceSixfoldAmbient f g h i :=
  F.leftIntermediateSupportInclusion G H ≫ correspondenceFirstDiagonalInclusion f g h i

instance [IsSeparated g] : IsClosedImmersion (F.leftIntermediateAmbientInclusion G H) :=
  inferInstanceAs (IsClosedImmersion
    (F.leftIntermediateSupportInclusion G H ≫ correspondenceFirstDiagonalInclusion f g h i))

/-- The first-stage ideal is the sum of the actual first-diagonal and exterior
coefficient ideals, preserving nilpotents and all embedded support. -/
theorem ker_leftIntermediateAmbientInclusion [IsSeparated g] :
    (F.leftIntermediateAmbientInclusion G H).ker =
      (correspondenceFirstDiagonalInclusion f g h i).ker ⊔
        (F.tripleSupportProductInclusion G H).ker :=
  ker_comp_eq_sup_of_isPullback _ _ _ _ (F.leftIntermediate_ambient_isPullback G H)

/-- Actual triple incidence embeds in the fourfold product using its original
pair-incidence and third-support coordinates. -/
def tripleIncidenceFourfoldInclusion : F.tripleIncidence G H ⟶
    correspondenceFourfoldProduct f g h i :=
  pullback.map _ _ _ _ (F.incidenceInclusion G) H.inclusion (𝟙 Z)
    (by simp [incidenceTarget, correspondenceTripleTarget])
    (by simp [projection, correspondenceProjection])

set_option backward.isDefEq.respectTransparency false in
instance : IsClosedImmersion (F.tripleIncidenceFourfoldInclusion G H) := by
  unfold tripleIncidenceFourfoldInclusion
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion (F.incidenceInclusion G)))
    (inferInstanceAs (IsClosedImmersion H.inclusion)) (by simp)
    (by simp [projection, correspondenceProjection])

/-- The actual fourfold inclusion preserves the original pair-incidence coordinate. -/
@[reassoc (attr := simp)] theorem tripleIncidenceFourfoldInclusion_fst :
    F.tripleIncidenceFourfoldInclusion G H ≫
      pullback.fst (correspondenceTripleTarget f g h) (pullback.fst h i) =
    F.tripleIncidenceFst G H ≫ F.incidenceInclusion G := pullback.lift_fst _ _ _

/-- The actual fourfold inclusion preserves the original third-support coordinate. -/
@[reassoc (attr := simp)] theorem tripleIncidenceFourfoldInclusion_snd :
    F.tripleIncidenceFourfoldInclusion G H ≫
      pullback.snd (correspondenceTripleTarget f g h) (pullback.fst h i) =
    F.tripleIncidenceSnd G H ≫ H.inclusion := pullback.lift_snd _ _ _

/-- The remaining-diagonal support embedding keeps the original third support. -/
@[reassoc (attr := simp)] theorem tripleIncidenceToLeftSupportProduct_snd :
    F.tripleIncidenceToLeftSupportProduct G H ≫
      pullback.snd (F.incidenceTarget G ≫ h) (H.projection ≫ h) =
    F.tripleIncidenceSnd G H := by
  simp only [tripleIncidenceToLeftSupportProduct, pullback.mapDesc, pullback.map,
    pullback.lift_snd, Category.comp_id, tripleIncidenceSnd]

/-- The remaining diagonal and the genuine first-stage support give the same
ambient morphism on actual triple incidence. -/
@[reassoc] theorem tripleIncidence_firstDiagonal_comm :
    F.tripleIncidenceFourfoldInclusion G H ≫ correspondenceSecondDiagonalInclusion f g h i =
    F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateSupportInclusion G H := by
  apply pullback.hom_ext <;> simp

/-- The remaining diagonal cuts out exactly the full actual triple-incidence
scheme from the first-stage support product. -/
theorem tripleIncidence_firstDiagonal_isPullback :
    IsPullback (F.tripleIncidenceFourfoldInclusion G H)
      (F.tripleIncidenceToLeftSupportProduct G H)
      (correspondenceSecondDiagonalInclusion f g h i)
      (F.leftIntermediateSupportInclusion G H) where
  w := F.tripleIncidence_firstDiagonal_comm G H
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun c ↦ by
    have ha := congrArg (fun m => m ≫
      pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h)) c.condition
    have hb := congrArg (fun m => m ≫
      pullback.snd (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h)) c.condition
    simp only [Category.assoc, correspondenceSecondDiagonalInclusion, pullback.mapDesc,
      pullback.map, pullback.lift_fst, Category.comp_id,
      leftIntermediateSupportInclusion_fst] at ha
    simp only [Category.assoc, correspondenceSecondDiagonalInclusion, pullback.mapDesc,
      pullback.map, pullback.lift_snd, Category.comp_id,
      leftIntermediateSupportInclusion_snd] at hb
    have hbase :
        (c.snd ≫ pullback.fst (F.incidenceTarget G ≫ h) (H.projection ≫ h)) ≫
          F.incidenceTarget G =
        (c.snd ≫ pullback.snd (F.incidenceTarget G ≫ h) (H.projection ≫ h)) ≫ H.projection := by
      calc
        _ = (c.snd ≫ pullback.fst _ _ ≫ F.incidenceInclusion G) ≫
            correspondenceTripleTarget f g h := by
          simp [correspondenceTripleTarget, incidenceTarget]
        _ = (c.fst ≫ pullback.fst _ _) ≫ correspondenceTripleTarget f g h := by rw [ha]
        _ = (c.fst ≫ pullback.snd _ _) ≫ pullback.fst h i := by
          simp only [Category.assoc, pullback.condition]
        _ = _ := by rw [hb]; rfl
    let w : c.pt ⟶ F.tripleIncidence G H :=
      pullback.lift (c.snd ≫ pullback.fst _ _) (c.snd ≫ pullback.snd _ _) hbase
    have hw₁ : w ≫ F.tripleIncidenceFourfoldInclusion G H = c.fst := by
      apply pullback.hom_ext
      · simpa only [Category.assoc, tripleIncidenceFourfoldInclusion_fst,
          tripleIncidenceFst, w, pullback.lift_fst_assoc] using ha.symm
      · simpa only [Category.assoc, tripleIncidenceFourfoldInclusion_snd,
          tripleIncidenceSnd, w, pullback.lift_snd_assoc] using hb.symm
    have hw₂ : w ≫ F.tripleIncidenceToLeftSupportProduct G H = c.snd := by
      apply pullback.hom_ext
      · simp only [Category.assoc, w, pullback.lift_fst, Category.comp_id]
      · simp only [Category.assoc, w, pullback.lift_snd, Category.comp_id]
    refine ⟨w, hw₁, hw₂, ?_⟩
    intro m hm _
    exact (cancel_mono (F.tripleIncidenceFourfoldInclusion G H)).mp (hm.trans hw₁.symm))⟩

/-- The complete triple-incidence embedding into the six-factor ambient. -/
abbrev tripleIncidenceSixfoldInclusion : F.tripleIncidence G H ⟶
    correspondenceSixfoldAmbient f g h i :=
  F.tripleIncidenceFourfoldInclusion G H ≫
    correspondenceSecondDiagonalInclusion f g h i ≫ correspondenceFirstDiagonalInclusion f g h i

instance [IsSeparated g] [IsSeparated h] :
    IsClosedImmersion (F.tripleIncidenceSixfoldInclusion G H) :=
  inferInstanceAs (IsClosedImmersion (F.tripleIncidenceFourfoldInclusion G H ≫
    correspondenceSecondDiagonalInclusion f g h i ≫ correspondenceFirstDiagonalInclusion f g h i))

/-- The full actual triple incidence is the Cartesian intersection of the
combined two diagonals with the original exterior coefficient support. -/
theorem tripleIncidence_sixfold_isPullback :
    IsPullback (F.tripleIncidenceFourfoldInclusion G H)
      (F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateToTripleSupport G H)
      (correspondenceSecondDiagonalInclusion f g h i ≫ correspondenceFirstDiagonalInclusion f g h i)
      (F.tripleSupportProductInclusion G H) :=
  (F.tripleIncidence_firstDiagonal_isPullback G H).paste_vert
    (F.leftIntermediate_ambient_isPullback G H)

/-- In the first-diagonal ambient the full actual triple ideal is the sum
of the remaining diagonal ideal and the first-stage support ideal. -/
theorem ker_tripleIncidenceFirstDiagonalInclusion [IsSeparated h] :
    (F.tripleIncidenceFourfoldInclusion G H ≫ correspondenceSecondDiagonalInclusion f g h i).ker =
      (correspondenceSecondDiagonalInclusion f g h i).ker ⊔
        (F.leftIntermediateSupportInclusion G H).ker :=
  ker_comp_eq_sup_of_isPullback _ _ _ _ (F.tripleIncidence_firstDiagonal_isPullback G H)

/-- The actual six-factor triple ideal retains the combined diagonal ideal
and the original exterior coefficient ideal, without passing to reductions. -/
theorem ker_tripleIncidenceSixfoldInclusion [IsSeparated g] [IsSeparated h] :
    (F.tripleIncidenceSixfoldInclusion G H).ker =
      (correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceFirstDiagonalInclusion f g h i).ker ⊔
          (F.tripleSupportProductInclusion G H).ker :=
  ker_comp_eq_sup_of_isPullback _ _ _ _ (F.tripleIncidence_sixfold_isPullback G H)

end FiniteCorrespondenceGenerator

end Motivic
