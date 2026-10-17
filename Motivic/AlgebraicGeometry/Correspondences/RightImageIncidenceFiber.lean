/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RightIntermediateDiagonalLists
public import Motivic.AlgebraicGeometry.Cycles.GenericFiniteFiber
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Genuine right final-incidence base change and full fibers

The original full triple incidence maps to first-support times the last
pair's actual scheme image over Y. This map is finite because it is the
Cartesian base change of the original finite right image-product map.
Every branch above a generic final-incidence image has a proved generic
triple-incidence lift. No projection to the right pair is assumed finite.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The original first support incident with the full last-pair scheme image. -/
abbrev rightImageIncidence : Scheme.{u} :=
  pullback F.targetProjection ((G.incidenceMap H).imageι ≫ pullback.fst g i)

/-- The genuine Y-diagonal inclusion on the actual right image-product scheme. -/
abbrev rightImageIncidenceInclusion : F.rightImageIncidence G H ⟶
    F.rightIntermediateImageProduct G H :=
  pullback.mapDesc F.targetProjection ((G.incidenceMap H).imageι ≫ pullback.fst g i) g

instance [IsSeparated g] : IsClosedImmersion (F.rightImageIncidenceInclusion G H) :=
  inferInstanceAs (IsClosedImmersion
    (pullback.mapDesc F.targetProjection ((G.incidenceMap H).imageι ≫ pullback.fst g i) g))

/-- The literal Y coordinate on right image-side final incidence. -/
abbrev rightImageIncidenceMiddle : F.rightImageIncidence G H ⟶ Y :=
  pullback.fst F.targetProjection ((G.incidenceMap H).imageι ≫ pullback.fst g i) ≫
    F.targetProjection

/-- The actual full-incidence map uses only the established associator, the
unchanged first support, and the last-pair scheme-image factor. -/
def tripleToRightImageIncidence : F.tripleIncidence G H ⟶ F.rightImageIncidence G H :=
  (F.tripleIncidenceAssoc G H).hom ≫
    pullback.map _ _ _ _ (𝟙 F.scheme) (G.incidenceMap H).toImage (𝟙 Y)
      (by simp) (by simp)

/-- The full-incidence image map retains the first original support. -/
@[reassoc (attr := simp)] theorem tripleToRightImageIncidence_fst :
    F.tripleToRightImageIncidence G H ≫
      pullback.fst F.targetProjection ((G.incidenceMap H).imageι ≫ pullback.fst g i) =
    F.tripleIncidenceFst G H ≫ F.incidenceFst G := by
  simp [tripleToRightImageIncidence, pullback.map, pullback.lift_fst]

/-- The full-incidence image map retains the actual last-pair image factor. -/
@[reassoc (attr := simp)] theorem tripleToRightImageIncidence_snd :
    F.tripleToRightImageIncidence G H ≫
      pullback.snd F.targetProjection ((G.incidenceMap H).imageι ≫ pullback.fst g i) =
    F.tripleIncidenceToRightPair G H ≫ (G.incidenceMap H).toImage := by
  simp [tripleToRightImageIncidence, pullback.map, pullback.lift_snd]

/-- The image-side remaining inclusion retains the first-support coordinate. -/
@[reassoc (attr := simp)] theorem rightImageIncidenceInclusion_fst :
    F.rightImageIncidenceInclusion G H ≫
      pullback.fst (F.targetProjection ≫ g)
        ((G.incidenceMap H).imageι ≫ pullback.fst g i ≫ g) =
    pullback.fst F.targetProjection ((G.incidenceMap H).imageι ≫ pullback.fst g i) := by
  change pullback.mapDesc F.targetProjection ((G.incidenceMap H).imageι ≫ pullback.fst g i) g ≫
    pullback.fst (F.targetProjection ≫ g) (((G.incidenceMap H).imageι ≫ pullback.fst g i) ≫ g) = _
  simp only [pullback.mapDesc, pullback.map, pullback.lift_fst, Category.comp_id]

/-- The image-side remaining inclusion retains the full actual last-pair image. -/
@[reassoc (attr := simp)] theorem rightImageIncidenceInclusion_snd :
    F.rightImageIncidenceInclusion G H ≫
      pullback.snd (F.targetProjection ≫ g)
        ((G.incidenceMap H).imageι ≫ pullback.fst g i ≫ g) =
    pullback.snd F.targetProjection ((G.incidenceMap H).imageι ≫ pullback.fst g i) := by
  change pullback.mapDesc F.targetProjection ((G.incidenceMap H).imageι ≫ pullback.fst g i) g ≫
    pullback.snd (F.targetProjection ≫ g) (((G.incidenceMap H).imageι ≫ pullback.fst g i) ≫ g) = _
  simp only [pullback.mapDesc, pullback.map, pullback.lift_snd, Category.comp_id]

/-- Image-side right final incidence is the original remaining Y-diagonal pullback. -/
theorem rightImageIncidenceRemaining_isPullback :
    IsPullback (F.rightImageIncidenceMiddle G H) (F.rightImageIncidenceInclusion G H)
      (pullback.diagonal g) (F.rightImageMiddlePair G H) :=
  pullback_map_diagonal_isPullback
    F.targetProjection ((G.incidenceMap H).imageι ≫ pullback.fst g i) g

/-- The full-incidence image map retains its actual original remaining Y coordinate. -/
@[reassoc] theorem tripleToRightImageIncidence_middle :
    F.tripleToRightImageIncidence G H ≫ F.rightImageIncidenceMiddle G H =
      F.tripleIncidenceFst G H ≫ F.incidenceFst G ≫ F.targetProjection := by
  simp [rightImageIncidenceMiddle]

/-- Both actual remaining inclusions commute with the original finite image-product map. -/
@[reassoc] theorem tripleToRightImageIncidence_square :
    F.tripleToRightImageIncidence G H ≫ F.rightImageIncidenceInclusion G H =
      F.tripleIncidenceToRightSupportProduct G H ≫ F.rightIntermediateImageMap G H := by
  apply pullback.hom_ext <;> simp

/-- Original full triple incidence is the Cartesian inverse image of the genuine
right final image incidence under the original finite image-product map. -/
theorem tripleToRightImageIncidence_isPullback :
    IsPullback (F.tripleToRightImageIncidence G H)
      (F.tripleIncidenceToRightSupportProduct G H)
      (F.rightImageIncidenceInclusion G H) (F.rightIntermediateImageMap G H) := by
  apply IsPullback.of_right (t := F.rightImageIncidenceRemaining_isPullback G H)
  · simpa only [F.tripleToRightImageIncidence_middle G H,
      F.rightIntermediateImageMap_middlePair G H] using F.rightRemainingDiagonal_isPullback G H
  · exact F.tripleToRightImageIncidence_square G H

/-- This actual final map is finite by genuine Cartesian base change of
id_F times the last-pair image factor. The right-pair projection is not used. -/
instance [IsSeparated i] : IsFinite (F.tripleToRightImageIncidence G H) :=
  MorphismProperty.of_isPullback (F.tripleToRightImageIncidence_isPullback G H).flip
    (inferInstanceAs (IsFinite (F.rightIntermediateImageMap G H)))

/-- Every right final-incidence point supplies an actual Y-diagonal range witness. -/
theorem rightImageIncidence_middle_mem_diagonal (y : F.rightImageIncidence G H) :
    ∃ z : Y, pullback.diagonal g z =
      F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y) :=
  ⟨F.rightImageIncidenceMiddle G H y,
    congrArg (fun k => k y) (F.rightImageIncidenceRemaining_isPullback G H).w⟩

/-- Smoothness chooses one genuine remaining Y-diagonal list at an actual
right image-incidence point, without a supplied diagonal-range witness. -/
theorem exists_rightImageIncidenceRemainingList [Smooth g] [IsSeparated g]
    (y : F.rightImageIncidence G H) :
    ∃ s : List ((pullback g g).presheaf.stalk
        (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y))),
      RingTheory.Sequence.IsRegular ((pullback g g).presheaf.stalk
        (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y))) s ∧
      (pullback.diagonal g).ker.stalk
        (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y)) = Ideal.ofList s := by
  obtain ⟨z, hz⟩ := F.rightImageIncidence_middle_mem_diagonal G H y
  have hex : ∃ s : List ((pullback g g).presheaf.stalk (pullback.diagonal g z)),
      RingTheory.Sequence.IsRegular
        ((pullback g g).presheaf.stalk (pullback.diagonal g z)) s ∧
      (pullback.diagonal g).ker.stalk (pullback.diagonal g z) = Ideal.ofList s := by
    obtain ⟨s, hs, hker⟩ := Diagonal.exists_regular_kernel_of_smooth g z
    exact ⟨s, hs, ((pullback.diagonal g).ker_stalk z).trans hker⟩
  exact (congrArg (fun q : (pullback g g : Scheme.{u}) =>
    ∃ s : List ((pullback g g).presheaf.stalk q),
      RingTheory.Sequence.IsRegular ((pullback g g).presheaf.stalk q) s ∧
        (pullback.diagonal g).ker.stalk q = Ideal.ofList s) hz).mp hex

/-- Every point of the whole ambient finite fiber lifts to the actual original
triple incidence, with both literal point projections retained. -/
theorem rightImageIncidenceFiber_lift (y : F.rightImageIncidence G H)
    (x : F.rightIntermediateSupportProduct G H)
    (hx : F.rightIntermediateImageMap G H x = F.rightImageIncidenceInclusion G H y) :
    ∃ w : F.tripleIncidence G H,
      F.tripleToRightImageIncidence G H w = y ∧
        F.tripleIncidenceToRightSupportProduct G H w = x :=
  Scheme.exists_preimage_of_isPullback
    (F.tripleToRightImageIncidence_isPullback G H) y x hx.symm

/-- The whole ambient point fiber is identified with the whole final-incidence
fiber. This is only an equivalence of point sets, never a splitting of rings. -/
def rightImageIncidenceFiberEquiv [IsSeparated g] (y : F.rightImageIncidence G H) :
    {w : F.tripleIncidence G H // F.tripleToRightImageIncidence G H w = y} ≃
      {x : F.rightIntermediateSupportProduct G H //
        F.rightIntermediateImageMap G H x = F.rightImageIncidenceInclusion G H y} :=
  Equiv.ofBijective
    (fun w => ⟨F.tripleIncidenceToRightSupportProduct G H w.1, by
      rw [← Scheme.Hom.comp_apply, ← F.tripleToRightImageIncidence_square G H,
        Scheme.Hom.comp_apply, w.2]⟩)
    ⟨fun w v he => Subtype.ext
      ((F.tripleIncidenceToRightSupportProduct G H).isClosedEmbedding.injective
        (congrArg Subtype.val he)), by
      intro x
      obtain ⟨w, hw, hx⟩ := F.rightImageIncidenceFiber_lift G H y x.1 x.2
      exact ⟨⟨w, hw⟩, Subtype.ext hx⟩⟩

/-- The fiber equivalence retains the actual original remaining-inclusion map. -/
@[simp] theorem rightImageIncidenceFiberEquiv_apply_val [IsSeparated g]
    (y : F.rightImageIncidence G H)
    (w : {w : F.tripleIncidence G H // F.tripleToRightImageIncidence G H w = y}) :
    (F.rightImageIncidenceFiberEquiv G H y w).1 =
      F.tripleIncidenceToRightSupportProduct G H w.1 := rfl

/-- Every actual source point over a generic final image-incidence point is
generic in the original triple incidence, by finite genericity reflection. -/
theorem triple_mem_genericPoints_of_rightImage [IsSeparated i]
    (w : F.tripleIncidence G H)
    (hw : F.tripleToRightImageIncidence G H w ∈ genericPoints (F.rightImageIncidence G H)) :
    w ∈ genericPoints (F.tripleIncidence G H) :=
  mem_genericPoints_of_image_generic (F.tripleToRightImageIncidence G H) w hw

/-- The complete ambient fiber above a generic final image-incidence point has
actual generic triple-incidence lifts; genericity is proved, not supplied. -/
theorem rightImageIncidenceFiber_lift_generic [IsSeparated i]
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (x : F.rightIntermediateSupportProduct G H)
    (hx : F.rightIntermediateImageMap G H x = F.rightImageIncidenceInclusion G H y) :
    ∃ w : F.tripleIncidence G H, w ∈ genericPoints (F.tripleIncidence G H) ∧
      F.tripleToRightImageIncidence G H w = y ∧
        F.tripleIncidenceToRightSupportProduct G H w = x := by
  obtain ⟨w, hw, hx⟩ := F.rightImageIncidenceFiber_lift G H y x hx
  exact ⟨w, F.triple_mem_genericPoints_of_rightImage G H w (hw.symm ▸ hy), hw, hx⟩

end Motivic.FiniteCorrespondenceGenerator
