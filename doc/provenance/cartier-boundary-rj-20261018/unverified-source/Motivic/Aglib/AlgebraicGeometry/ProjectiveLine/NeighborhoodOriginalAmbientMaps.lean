/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodPunctureBaseChange

/-! # Original ambient maps for the zero-neighborhood correction

The lambda source maps to the literal original open. Its puncture square and
coefficient-base-change square commute before applying any presheaf. The whole
zero section over the retained principal base open is constructed explicitly.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace AlgebraicGeometry.RelativeProjectiveLine

variable (k R : Type u) [Field k] [CommRing R]
  (b : Spec (.of R) ⟶ Spec (.of k)) [Smooth b]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]

/-- The actual original affine open with its unchanged field structure. -/
def neighborhoodAmbientSite : SmoothSite (Spec (.of k)) := by
  have : Smooth ((V.ι ≫ Scheme.Hom.boundaryLineProjection R) ≫ b) :=
    neighborhood_open_line_smooth k R b V.ι
  exact SmoothSite.mk ((V.ι ≫ Scheme.Hom.boundaryLineProjection R) ≫ b)

/-- The lambda correction is an ambient section on an actual open of the original open. -/
def neighborhoodLambdaToAmbient (r : R) :
    neighborhoodLambdaSite k R b V r ⟶ neighborhoodAmbientSite k R b V :=
  SmoothSite.homMk (neighborhoodSourceOpen R V r).ι (by
    change (neighborhoodSourceOpen R V r).ι ≫
        ((V.ι ≫ Scheme.Hom.boundaryLineProjection R) ≫ b) =
      ((neighborhoodSourceOpen R V r).ι ≫ neighborhoodProjection R V) ≫ b
    simp only [neighborhoodProjection, neighborhoodInclusion, Category.assoc,
      chart_toSpec, Scheme.Hom.boundaryLineProjection])

/-- Literal puncture inclusion into the original affine open. -/
def neighborhoodPunctureToAmbient :
    neighborhoodCommonSite k R b V 1 ⟶ neighborhoodAmbientSite k R b V :=
  SmoothSite.homMk (commonNeighborhoodToV R V 1) (by
    change commonNeighborhoodToV R V 1 ≫ ((V.ι ≫ _) ≫ b) =
      ((commonNeighborhoodSource R V 1).ι ≫ _) ≫ b
    simp only [Category.assoc, commonNeighborhoodToV_ι_assoc])

/-- The original puncture restriction and lambda inclusion give the same ambient map. -/
@[reassoc] theorem neighborhoodOriginalRestriction_ambient (r : R) :
    neighborhoodOriginalRestriction R V k b r ≫ neighborhoodPunctureToAmbient k R b V =
      neighborhoodPencilAlpha k R b V r ≫ neighborhoodLambdaToAmbient k R b V r := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono V.ι).mp
  change ((neighborhoodOriginalRestriction R V k b r).left ≫
      commonNeighborhoodToV R V 1) ≫ V.ι =
    (commonNeighborhoodToSectionSource R V r ≫ (neighborhoodSourceOpen R V r).ι) ≫ V.ι
  simp only [Category.assoc, commonNeighborhoodToV_ι, commonNeighborhoodToSectionSource_ι_assoc,
    neighborhoodOriginalRestriction_ι]

omit [IsAffine V.toScheme] in
/-- The common correction source is the actual puncture of the lambda ambient,
not merely a map into that puncture with the same point support. -/
theorem commonNeighborhoodPuncture_isPullback (r : R) :
    IsPullback (commonNeighborhoodToPsi R V r) (commonNeighborhoodToSectionSource R V r)
      (fixedPsiSource R r).ι ((neighborhoodSourceOpen R V r).ι ≫ V.ι) := by
  have : IsOpenImmersion (commonNeighborhoodToSectionSource R V r) := by
    have : IsOpenImmersion (commonNeighborhoodToSectionSource R V r ≫
        (neighborhoodSourceOpen R V r).ι) := by
      rw [commonNeighborhoodToSectionSource_ι]
      infer_instance
    exact IsOpenImmersion.of_comp _ (neighborhoodSourceOpen R V r).ι
  apply IsOpenImmersion.isPullback
  · simp only [commonNeighborhoodToSectionSource_ι_assoc, commonNeighborhoodToV_ι,
      commonNeighborhoodToPsi_ι]
  · ext y
    change ((neighborhoodSourceOpen R V r).ι ≫ V.ι) y ∈
        (fixedPsiSource R r).ι.opensRange ↔
      y ∈ (commonNeighborhoodToSectionSource R V r).opensRange
    rw [Scheme.Opens.opensRange_ι]
    constructor
    · intro hy
      let x : (commonNeighborhoodSource R V r).toScheme :=
        ⟨y.val.val, y.val.property, hy⟩
      refine ⟨x, ?_⟩
      apply ((neighborhoodSourceOpen R V r).ι ≫ V.ι).isOpenEmbedding.injective
      change (commonNeighborhoodToSectionSource R V r ≫
        (neighborhoodSourceOpen R V r).ι ≫ V.ι) x = y.val.val
      rw [commonNeighborhoodToSectionSource_ι_assoc, commonNeighborhoodToV_ι]
      rfl
    · rintro ⟨x, rfl⟩
      change (commonNeighborhoodToSectionSource R V r ≫
        (neighborhoodSourceOpen R V r).ι ≫ V.ι) x ∈ fixedPsiSource R r
      rw [commonNeighborhoodToSectionSource_ι_assoc, commonNeighborhoodToV_ι]
      exact x.property.2

variable {S : Type u} [CommRing S] (f : R →+* S)
  [Smooth (Spec.map (CommRingCat.ofHom f) ≫ b)]
  [IsAffine (neighborhoodBaseChangeOpen f V).toScheme]

/-- Actual coefficient extension on the ambient open, paired with puncture restriction. -/
def neighborhoodAmbientBaseChange :
    neighborhoodAmbientSite k S (Spec.map (CommRingCat.ofHom f) ≫ b)
      (neighborhoodBaseChangeOpen f V) ⟶ neighborhoodAmbientSite k R b V :=
  SmoothSite.homMk (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ∣_ V) (by
    change (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ∣_ V) ≫
        ((V.ι ≫ Scheme.Hom.boundaryLineProjection R) ≫ b) =
      (((neighborhoodBaseChangeOpen f V).ι ≫ Scheme.Hom.boundaryLineProjection S) ≫
        (Spec.map (CommRingCat.ofHom f) ≫ b))
    simp only [Category.assoc, morphismRestrict_ι_assoc, polynomial_scalar_projection_assoc])

/-- Puncturing and restricting the original coefficient base commute on the nose as maps. -/
@[reassoc] theorem neighborhoodPunctureBaseChange_ambient :
    neighborhoodPunctureBaseChange f V k b ≫ neighborhoodPunctureToAmbient k R b V =
      neighborhoodPunctureToAmbient k S (Spec.map (CommRingCat.ofHom f) ≫ b)
        (neighborhoodBaseChangeOpen f V) ≫ neighborhoodAmbientBaseChange k R b V f := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono V.ι).mp
  change (neighborhoodPunctureBaseChangeScheme f V ≫ commonNeighborhoodToV R V 1) ≫ V.ι =
    (commonNeighborhoodToV S (neighborhoodBaseChangeOpen f V) 1 ≫
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ∣_ V)) ≫ V.ι
  simp only [Category.assoc, commonNeighborhoodToV_ι,
    neighborhoodPunctureBaseChangeScheme_ι, morphismRestrict_ι,
    commonNeighborhoodToV_ι_assoc]

/-- This is the precise ambient square used after the true coefficient-base shrink. -/
@[reassoc] theorem neighborhoodBaseRestriction_ambient (r : S) :
    (neighborhoodOriginalRestriction S (neighborhoodBaseChangeOpen f V) k
        (Spec.map (CommRingCat.ofHom f) ≫ b) r ≫ neighborhoodPunctureBaseChange f V k b) ≫
      neighborhoodPunctureToAmbient k R b V =
    neighborhoodPencilAlpha k S (Spec.map (CommRingCat.ofHom f) ≫ b)
        (neighborhoodBaseChangeOpen f V) r ≫
      (neighborhoodLambdaToAmbient k S (Spec.map (CommRingCat.ofHom f) ≫ b)
        (neighborhoodBaseChangeOpen f V) r ≫ neighborhoodAmbientBaseChange k R b V f) := by
  rw [Category.assoc, neighborhoodPunctureBaseChange_ambient,
    ← Category.assoc, neighborhoodOriginalRestriction_ambient, Category.assoc]

omit [IsAffine V.toScheme] in
@[reassoc (attr := simp)] theorem neighborhoodZero_projection
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V) :
    neighborhoodZero R V hV ≫ neighborhoodProjection R V = 𝟙 _ := by
  rw [neighborhoodProjection, ← Category.assoc, neighborhoodZero_inclusion,
    zeroSection_toSpec]

variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
  (r : R)

/-- The whole original zero section on the retained base, not just its support. -/
def neighborhoodLambdaZero :
    Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ⟶
    (neighborhoodSourceOpen R V r).toScheme :=
  IsOpenImmersion.lift (neighborhoodSourceOpen R V r).ι
    (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫ neighborhoodZero R V hV) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      change (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫
        neighborhoodZero R V hV ≫
        neighborhoodProjection R V) x ∈ PrimeSpectrum.basicOpen r
      rw [neighborhoodZero_projection, Category.comp_id]
      exact x.property)

omit [IsAffine V.toScheme] in
@[reassoc (attr := simp)] theorem neighborhoodLambdaZero_ι :
    neighborhoodLambdaZero R V hV r ≫ (neighborhoodSourceOpen R V r).ι =
      Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫ neighborhoodZero R V hV :=
  IsOpenImmersion.lift_fac _ _ _

omit [IsAffine V.toScheme] in
/-- The resulting marking is exactly the original polynomial zero morphism. -/
@[reassoc] theorem neighborhoodLambdaZero_original :
    neighborhoodLambdaZero R V hV r ≫ (neighborhoodSourceOpen R V r).ι ≫ V.ι =
      Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) := by
  rw [neighborhoodLambdaZero_ι_assoc, neighborhoodZero_ι]

end AlgebraicGeometry.RelativeProjectiveLine
