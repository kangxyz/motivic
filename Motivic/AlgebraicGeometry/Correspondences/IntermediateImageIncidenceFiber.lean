/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RemainingDiagonalSupport
public import Motivic.AlgebraicGeometry.Cycles.GenericFiniteFiber
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Actual final-incidence fibers of the finite intermediate-image map

The remaining incidence on the actual intermediate scheme image is a genuine
pullback over the second middle object. The map from original triple incidence
is the base change of the actual finite support-product image map. Every point
of the entire ambient source fiber has a unique lift to that final incidence.
Above a generic final image-incidence point these lifts are genuinely generic,
by finite-fiber genericity reflection. No residue-field choice, component
dimension, reduction, or product-of-localizations assertion is assumed.
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

/-- The remaining incidence formed using the full actual intermediate scheme
image, retaining its original scheme structure. -/
abbrev leftImageIncidence : Scheme.{u} :=
  pullback ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection

/-- The genuine remaining-diagonal inclusion on the intermediate image product. -/
abbrev leftImageIncidenceInclusion : F.leftImageIncidence G H ⟶
    F.leftIntermediateImageProduct G H :=
  pullback.mapDesc ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection h

instance [IsSeparated h] : IsClosedImmersion (F.leftImageIncidenceInclusion G H) :=
  inferInstanceAs (IsClosedImmersion
    (pullback.mapDesc ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection h))

/-- The actual middle-object map of the image-side final incidence. -/
abbrev leftImageIncidenceMiddle : F.leftImageIncidence G H ⟶ Z :=
  pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection ≫
    (F.incidenceMap G).imageι ≫ pullback.snd f h

/-- Original triple incidence maps to image-side final incidence by the actual
pair-to-image morphism and the unchanged third support. -/
def tripleToLeftImageIncidence : F.tripleIncidence G H ⟶ F.leftImageIncidence G H :=
  pullback.map _ _ _ _ (F.incidenceMap G).toImage (𝟙 H.scheme) (𝟙 Z)
    (by simp) (by simp)

/-- The first projection of the final-incidence map is the original image factor. -/
@[reassoc (attr := simp)] theorem tripleToLeftImageIncidence_fst :
    F.tripleToLeftImageIncidence G H ≫
      pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection =
    F.tripleIncidenceFst G H ≫ (F.incidenceMap G).toImage :=
  pullback.lift_fst _ _ _

/-- The final-incidence map keeps the original third-support point. -/
@[reassoc (attr := simp)] theorem tripleToLeftImageIncidence_snd :
    F.tripleToLeftImageIncidence G H ≫
      pullback.snd ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection =
    F.tripleIncidenceSnd G H := by
  simp only [tripleToLeftImageIncidence, pullback.map, pullback.lift_snd,
    Category.comp_id, tripleIncidenceSnd]

/-- The image-side remaining inclusion remembers the original scheme-image coordinate. -/
@[reassoc (attr := simp)] theorem leftImageIncidenceInclusion_fst :
    F.leftImageIncidenceInclusion G H ≫
      pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd f h ≫ h)
        (H.projection ≫ h) =
    pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection := by
  change pullback.mapDesc ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection h ≫
    pullback.fst (((F.incidenceMap G).imageι ≫ pullback.snd f h) ≫ h) (H.projection ≫ h) = _
  simp only [pullback.mapDesc, pullback.map,
    pullback.lift_fst, Category.comp_id]

/-- The image-side remaining inclusion also retains the third support. -/
@[reassoc (attr := simp)] theorem leftImageIncidenceInclusion_snd :
    F.leftImageIncidenceInclusion G H ≫
      pullback.snd ((F.incidenceMap G).imageι ≫ pullback.snd f h ≫ h)
        (H.projection ≫ h) =
    pullback.snd ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection := by
  change pullback.mapDesc ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection h ≫
    pullback.snd (((F.incidenceMap G).imageι ≫ pullback.snd f h) ≫ h) (H.projection ≫ h) = _
  simp only [pullback.mapDesc, pullback.map,
    pullback.lift_snd, Category.comp_id]

/-- The image-side final incidence is the actual pullback of the remaining
middle diagonal, rather than just a topological intersection. -/
theorem leftImageIncidenceRemaining_isPullback :
    IsPullback (F.leftImageIncidenceMiddle G H) (F.leftImageIncidenceInclusion G H)
      (pullback.diagonal h) (F.leftImageMiddlePair G H) :=
  pullback_map_diagonal_isPullback
    ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection h

/-- The actual final-incidence image map preserves the original middle coordinate. -/
@[reassoc] theorem tripleToLeftImageIncidence_middle :
    F.tripleToLeftImageIncidence G H ≫ F.leftImageIncidenceMiddle G H =
      F.tripleIncidenceFst G H ≫ F.incidenceTarget G := by
  simp [leftImageIncidenceMiddle]

/-- The actual finite image map and both actual remaining inclusions commute. -/
@[reassoc] theorem tripleToLeftImageIncidence_square :
    F.tripleToLeftImageIncidence G H ≫ F.leftImageIncidenceInclusion G H =
      F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateImageMap G H := by
  apply pullback.hom_ext <;> simp

/-- The entire triple incidence is the Cartesian inverse image of the final
image incidence under the original finite support-product map. -/
theorem tripleToLeftImageIncidence_isPullback :
    IsPullback (F.tripleToLeftImageIncidence G H)
      (F.tripleIncidenceToLeftSupportProduct G H)
      (F.leftImageIncidenceInclusion G H) (F.leftIntermediateImageMap G H) := by
  apply IsPullback.of_right (t := F.leftImageIncidenceRemaining_isPullback G H)
  · simpa only [F.tripleToLeftImageIncidence_middle G H,
      F.leftIntermediateImageMap_middlePair G H] using F.remainingDiagonal_isPullback G H
  · exact F.tripleToLeftImageIncidence_square G H

/-- Finiteness is inherited by this actual Cartesian base change; no finiteness
of an individual source-stalk algebra is asserted. -/
instance [IsSeparated h] : IsFinite (F.tripleToLeftImageIncidence G H) :=
  MorphismProperty.of_isPullback (F.tripleToLeftImageIncidence_isPullback G H).flip
    (inferInstanceAs (IsFinite (F.leftIntermediateImageMap G H)))

/-- Every image-side final-incidence point gives an actual original-diagonal
point, allowing one fixed middle list to be chosen there. -/
theorem leftImageIncidence_middle_mem_diagonal (y : F.leftImageIncidence G H) :
    ∃ z : Z, pullback.diagonal h z =
      F.leftImageMiddlePair G H (F.leftImageIncidenceInclusion G H y) :=
  ⟨F.leftImageIncidenceMiddle G H y,
    congrArg (fun k => k y) (F.leftImageIncidenceRemaining_isPullback G H).w⟩

/-- Every point of the whole ambient finite fiber lifts to the actual original
triple incidence, with both literal point projections retained. -/
theorem leftImageIncidenceFiber_lift (y : F.leftImageIncidence G H)
    (x : F.leftIntermediateSupportProduct G H)
    (hx : F.leftIntermediateImageMap G H x = F.leftImageIncidenceInclusion G H y) :
    ∃ w : F.tripleIncidence G H,
      F.tripleToLeftImageIncidence G H w = y ∧
        F.tripleIncidenceToLeftSupportProduct G H w = x :=
  Scheme.exists_preimage_of_isPullback
    (F.tripleToLeftImageIncidence_isPullback G H) y x hx.symm

/-- The whole ambient point fiber is identified with the whole final-incidence
fiber. This is only an equivalence of point sets, never a splitting of rings. -/
def leftImageIncidenceFiberEquiv [IsSeparated h] (y : F.leftImageIncidence G H) :
    {w : F.tripleIncidence G H // F.tripleToLeftImageIncidence G H w = y} ≃
      {x : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H x = F.leftImageIncidenceInclusion G H y} :=
  Equiv.ofBijective
    (fun w => ⟨F.tripleIncidenceToLeftSupportProduct G H w.1, by
      rw [← Scheme.Hom.comp_apply, ← F.tripleToLeftImageIncidence_square G H,
        Scheme.Hom.comp_apply, w.2]⟩)
    ⟨fun w v he => Subtype.ext
      ((F.tripleIncidenceToLeftSupportProduct G H).isClosedEmbedding.injective
        (congrArg Subtype.val he)), by
      intro x
      obtain ⟨w, hw, hx⟩ := F.leftImageIncidenceFiber_lift G H y x.1 x.2
      exact ⟨⟨w, hw⟩, Subtype.ext hx⟩⟩

/-- The fiber equivalence retains the actual original remaining-inclusion map. -/
@[simp] theorem leftImageIncidenceFiberEquiv_apply_val [IsSeparated h]
    (y : F.leftImageIncidence G H)
    (w : {w : F.tripleIncidence G H // F.tripleToLeftImageIncidence G H w = y}) :
    (F.leftImageIncidenceFiberEquiv G H y w).1 =
      F.tripleIncidenceToLeftSupportProduct G H w.1 := rfl

/-- Every actual source point over a generic final image-incidence point is
generic in the original triple incidence, by finite genericity reflection. -/
theorem triple_mem_genericPoints_of_leftImage [IsSeparated h]
    (w : F.tripleIncidence G H)
    (hw : F.tripleToLeftImageIncidence G H w ∈ genericPoints (F.leftImageIncidence G H)) :
    w ∈ genericPoints (F.tripleIncidence G H) :=
  mem_genericPoints_of_image_generic (F.tripleToLeftImageIncidence G H) w hw

/-- The complete ambient fiber above a generic final image-incidence point has
actual generic triple-incidence lifts; genericity is proved, not supplied. -/
theorem leftImageIncidenceFiber_lift_generic [IsSeparated h]
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (x : F.leftIntermediateSupportProduct G H)
    (hx : F.leftIntermediateImageMap G H x = F.leftImageIncidenceInclusion G H y) :
    ∃ w : F.tripleIncidence G H, w ∈ genericPoints (F.tripleIncidence G H) ∧
      F.tripleToLeftImageIncidence G H w = y ∧
        F.tripleIncidenceToLeftSupportProduct G H w = x := by
  obtain ⟨w, hw, hx⟩ := F.leftImageIncidenceFiber_lift G H y x hx
  exact ⟨w, F.triple_mem_genericPoints_of_leftImage G H w (hw.symm ▸ hy), hw, hx⟩

end Motivic.FiniteCorrespondenceGenerator
