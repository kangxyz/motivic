/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Pencil.Sites
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # The retained projective target is the literal original punctured open -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RelativeProjectiveLine

variable (R : Type u) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens)

@[simp] theorem fixedPsiSource_one :
    fixedPsiSource R 1 = PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) := by
  simp only [fixedPsiSource, map_one, mul_one]

/-- With no base shrink, the common source is exactly the original punctured open. -/
@[simp] theorem commonNeighborhoodSource_one :
    commonNeighborhoodSource R V 1 = V ⊓
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) := by
  rw [commonNeighborhoodSource, fixedPsiSource_one]

/-- The retained graph is the original open inclusion through its affine chart. -/
instance commonNeighborhoodRetainedTargetMap_isOpenImmersion (r : R) :
    IsOpenImmersion (commonNeighborhoodRetainedTargetMap R V r) := by
  have : IsOpenImmersion (commonNeighborhoodRetainedTargetMap R V r ≫
      (neighborhoodRetainedOpen R V).ι) := by
    rw [commonNeighborhoodRetainedTargetMap_ι]
    exact inferInstanceAs (IsOpenImmersion
      ((commonNeighborhoodSource R V r).ι ≫ chart R ⟨0⟩))
  exact IsOpenImmersion.of_comp _ (neighborhoodRetainedOpen R V).ι

/-- Every retained target point lies in the literal original affine puncture. -/
theorem commonNeighborhoodRetainedTargetMap_one_surjective :
    Function.Surjective (commonNeighborhoodRetainedTargetMap R V 1) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := y.property.1
  change chart R ⟨0⟩ x = y.val at hxy
  have hxX : x ∈ PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) := by
    have hy : chart R ⟨0⟩ x ∈
        ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) ⟨1⟩ := by
      rw [hxy]
      exact y.property.2
    change x ∈ chart R ⟨0⟩ ⁻¹ᵁ
      ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) ⟨1⟩ at hy
    rwa [chart_preimage_other R ⟨0⟩ ⟨1⟩ (by decide)] at hy
  have hx' : x ∈ commonNeighborhoodSource R V 1 := by
    rw [commonNeighborhoodSource_one]
    exact ⟨hx, hxX⟩
  refine ⟨⟨x, hx'⟩, ?_⟩
  apply Subtype.ext
  have h := congrArg (fun f => f ⟨x, hx'⟩)
    (commonNeighborhoodRetainedTargetMap_ι R V 1)
  exact h.trans hxy

/-- The chart map identifies the actual original puncture with the retained target. -/
instance commonNeighborhoodRetainedTargetMap_one_isIso :
    IsIso (commonNeighborhoodRetainedTargetMap R V 1) := by
  have : Surjective (commonNeighborhoodRetainedTargetMap R V 1) :=
    ⟨commonNeighborhoodRetainedTargetMap_one_surjective R V⟩
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩

variable (k : Type u) [Field k] (b : Spec (.of R) ⟶ Spec (.of k)) [Smooth b]
  [IsAffine V.toScheme]

/-- The canonical comparison keeps the original field structure. -/
def neighborhoodPunctureIso :
    neighborhoodCommonSite k R b V 1 ≅ neighborhoodTargetSite k R b V :=
  MorphismProperty.Over.isoMk (asIso (commonNeighborhoodRetainedTargetMap R V 1))
    (MorphismProperty.Over.w (neighborhoodPencilGraph k R b V 1))

/-- Actual restriction between the original punctured open and its base-restricted open. -/
def neighborhoodOriginalRestriction (r : R) :
    neighborhoodCommonSite k R b V r ⟶ neighborhoodCommonSite k R b V 1 :=
  neighborhoodPencilGraph k R b V r ≫ (neighborhoodPunctureIso R V k b).inv

/-- Its composite with the affine open inclusion is the unchanged original inclusion. -/
@[reassoc] theorem neighborhoodOriginalRestriction_ι (r : R) :
    (neighborhoodOriginalRestriction R V k b r).left ≫
      (commonNeighborhoodSource R V 1).ι = (commonNeighborhoodSource R V r).ι := by
  apply (cancel_mono (chart R ⟨0⟩)).mp
  have h := congrArg (fun f => f.left)
    (show neighborhoodOriginalRestriction R V k b r ≫
      (neighborhoodPunctureIso R V k b).hom = neighborhoodPencilGraph k R b V r by
        simp only [neighborhoodOriginalRestriction, Category.assoc, Iso.inv_hom_id,
          Category.comp_id])
  change (neighborhoodOriginalRestriction R V k b r).left ≫
    commonNeighborhoodRetainedTargetMap R V 1 = commonNeighborhoodRetainedTargetMap R V r at h
  have h' := congrArg (fun f => f ≫ (neighborhoodRetainedOpen R V).ι) h
  simpa only [Category.assoc, commonNeighborhoodRetainedTargetMap_ι,
    commonNeighborhoodTargetMap] using h'

end AlgebraicGeometry.RelativeProjectiveLine
