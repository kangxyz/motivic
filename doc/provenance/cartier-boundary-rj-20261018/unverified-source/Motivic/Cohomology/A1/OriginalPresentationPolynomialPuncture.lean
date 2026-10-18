/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.OriginalPresentationOpenImage
public import Motivic.Cohomology.WholeAffineLineBaseSquareMaps
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodOriginalAmbientMaps

/-! # The original presentation puncture is the literal polynomial puncture

This comparison keeps the original field structure and the original polynomial
inclusion. It is the section-transport map between the étale correction and the
zero-neighborhood correction, not a sheafification or a new lifting hypothesis.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.RelativeProjectiveLine

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation

variable {k : Type u} [Field k] (R : Type u) [CommRing R]
  (b : Spec (.of R) ⟶ Spec (.of k)) [Smooth b]
  {Y Z : Scheme.{u}} {p : Y ⟶ Spec (.of (Polynomial R))}
  {z : Z ⟶ Spec (.of (Polynomial R))} {s : Z ⟶ Y}
  {x : Spec (.of (Polynomial R))}
  (e : OriginalEtalePresentation k (boundaryLineProjection R ≫ b) p
    (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) z s x)

local instance polynomialPunctureTarget : IsAffine e.target := e.target_affine
local instance polynomialPunctureRefinement : IsOpenImmersion e.refinement := e.refinement_open
local instance polynomialPunctureField : Smooth e.toField := e.base_smooth
local instance polynomialPunctureSmooth : SmoothOfRelativeDimension 1
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) := e.target_smooth
local instance polynomialPunctureAffine :
    IsAffine (Scheme.Opens.toScheme (X := Spec (.of (Polynomial R)))
    (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) :=
  IsAffineOpen.Spec_basicOpen _

variable (U : e.target.Opens) (V : (Spec e.base).Opens)
  [IsAffine V.toScheme]
  [IsAffine (boundaryBaseSourceOpen
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V).toScheme]

local instance polynomialPunctureRetainedAffine : IsAffine (retainedOriginalOpen e U V).toScheme :=
  retainedOriginalOpen_affine e U V

/-- The retained ambient target is the literal original affine open over the field. -/
def retainedPolynomialAmbientSiteIso :
    boundaryBaseAmbientSite k e.base e.toField
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V ≅
      neighborhoodAmbientSite k R b (retainedOriginalOpen e U V) :=
  MorphismProperty.Over.isoMk (retainedOriginalOpenIso e U V) (by
    rw [boundaryBaseAmbientSite_hom]
    change (retainedOriginalOpenIso e U V).hom ≫
        (((retainedOriginalOpen e U V).ι ≫ boundaryLineProjection R) ≫ b) =
      (boundaryBaseSourceOpen
        (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V).ι ≫
        (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) ≫ e.toField
    simp only [Category.assoc, retainedOriginalOpenIso_hom_ι_assoc]
    exact congrArg (fun f => (boundaryBaseSourceOpen
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V).ι ≫ f)
      e.base_compatibility)

/-- Scheme-level identification with the unchanged affine puncture consumed by
the zero-neighborhood lifting theorem. -/
def retainedPolynomialPunctureIso :
    (boundaryBaseCoverOpen
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
      (pullback.snd (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) e.refinement)
      U V).toScheme ≅
        (commonNeighborhoodSource R (retainedOriginalOpen e U V) 1).toScheme :=
  retainedOriginalPunctureIso e U V (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R)) ≪≫
    (Spec (.of (Polynomial R))).isoOfEq
      (commonNeighborhoodSource_one R (retainedOriginalOpen e U V)).symm

omit [Smooth b] [IsAffine V.toScheme]
  [IsAffine (boundaryBaseSourceOpen
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V).toScheme] in
@[reassoc (attr := simp)] theorem retainedPolynomialPunctureIso_hom_ι :
    (retainedPolynomialPunctureIso R b e U V).hom ≫
        (commonNeighborhoodSource R (retainedOriginalOpen e U V) 1).ι =
      (boundaryBaseCoverOpen
        (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
        (pullback.snd (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) e.refinement)
        U V).ι ≫ pullback.fst _ e.refinement ≫
          (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) := by
  simp [retainedPolynomialPunctureIso, Category.assoc]

/-- The canonical puncture comparison is over the same original field, so
restriction of sections of the original presheaf uses this exact isomorphism. -/
def retainedPolynomialPunctureSiteIso :
    boundaryBaseOpenSite k e.base e.toField
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
      (pullback.snd (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) e.refinement)
      U V ≅ neighborhoodCommonSite k R b (retainedOriginalOpen e U V) 1 :=
  MorphismProperty.Over.isoMk (retainedPolynomialPunctureIso R b e U V) (by
    have hfield := MorphismProperty.Over.w
      (boundaryBaseOpenRestriction k e.base e.toField
        (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
        (pullback.snd (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) e.refinement)
        U V)
    change _ = (boundaryBaseOpenSite k e.base e.toField
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
      (pullback.snd (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) e.refinement)
      U V).hom
    rw [← hfield]
    change (retainedPolynomialPunctureIso R b e U V).hom ≫
      (((commonNeighborhoodSource R (retainedOriginalOpen e U V) 1).ι ≫
        boundaryLineProjection R) ≫ b) =
      (boundaryBaseCoverOpen
        (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
        (pullback.snd (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) e.refinement)
        U V).ι ≫ pullback.snd _ e.refinement ≫
          e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _ ≫ e.toField
    simp only [Category.assoc, retainedPolynomialPunctureIso_hom_ι_assoc]
    rw [pullback.condition_assoc, e.base_compatibility])

/-- The puncture comparison preserves its actual ambient arrow. -/
@[reassoc] theorem retainedPolynomialPunctureSiteIso_ambient :
    (retainedPolynomialPunctureSiteIso R b e U V).hom ≫
      neighborhoodPunctureToAmbient k R b (retainedOriginalOpen e U V) =
    boundaryBaseOpenArrow k e.base e.toField
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
      (pullback.snd (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) e.refinement)
      U V ≫ (retainedPolynomialAmbientSiteIso R b e U V).hom := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono (retainedOriginalOpen e U V).ι).mp
  change ((retainedPolynomialPunctureIso R b e U V).hom ≫
      commonNeighborhoodToV R (retainedOriginalOpen e U V) 1) ≫
        (retainedOriginalOpen e U V).ι =
    (boundaryBaseCoverMap
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
      (pullback.snd (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) e.refinement)
      U V ≫ (retainedOriginalOpenIso e U V).hom) ≫ (retainedOriginalOpen e U V).ι
  simp only [Category.assoc, commonNeighborhoodToV_ι,
    retainedPolynomialPunctureIso_hom_ι, retainedOriginalOpenIso_hom_ι]
  simpa only [Category.assoc, retainedOriginalOpenIso_hom_ι] using
    (retainedOriginalPullback_isPullback e U V
      (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R)))).w.symm

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
