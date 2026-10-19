/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.Presentation.PolynomialPuncture
public import Motivic.Cohomology.A1.LocalVanishing.ZeroNeighborhood.OriginalPointLifting
public import Motivic.Cohomology.A1.Boundary.RestrictionDifference.Restriction

/-! # The second correction restricts the actual first presentation puncture

The true coefficient localization is performed on the original polynomial
base. Its ambient map and original-section map are transported through the
checked retained-open isomorphisms, retaining the entire new zero section.
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

local instance secondCorrectionTarget : IsAffine e.target := e.target_affine
local instance secondCorrectionRefinement : IsOpenImmersion e.refinement := e.refinement_open
local instance secondCorrectionField : Smooth e.toField := e.base_smooth
local instance secondCorrectionSmooth : SmoothOfRelativeDimension 1
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) := e.target_smooth
local instance secondCorrectionPunctureAffine :
    IsAffine (Scheme.Opens.toScheme (X := Spec (.of (Polynomial R)))
    (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) := IsAffineOpen.Spec_basicOpen _

variable (U : e.target.Opens) (V : (Spec e.base).Opens)
  [IsAffine V.toScheme]
  [IsAffine (boundaryBaseSourceOpen
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V).toScheme]

local instance secondCorrectionRetainedAffine : IsAffine (retainedOriginalOpen e U V).toScheme :=
  retainedOriginalOpen_affine e U V

section ScalarMap

variable {S : Type u} [CommRing S] (f : R →+* S)
  [Smooth (Spec.map (CommRingCat.ofHom f) ≫ b)]
  [IsAffine (neighborhoodBaseChangeOpen f (retainedOriginalOpen e U V)).toScheme] (t : S)

/-- The second correction restricts sections of the unchanged first puncture. -/
def retainedPolynomialSecondRestriction :
    neighborhoodCommonSite k S (Spec.map (CommRingCat.ofHom f) ≫ b)
      (neighborhoodBaseChangeOpen f (retainedOriginalOpen e U V)) t ⟶
    boundaryBaseOpenSite k e.base e.toField
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
      (pullback.snd (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
        (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) e.refinement) U V :=
  (neighborhoodOriginalRestriction S
      (neighborhoodBaseChangeOpen f (retainedOriginalOpen e U V)) k
      (Spec.map (CommRingCat.ofHom f) ≫ b) t ≫
    neighborhoodPunctureBaseChange f (retainedOriginalOpen e U V) k b) ≫
      (retainedPolynomialPunctureSiteIso R b e U V).inv

/-- Its ambient correction maps to the same retained first ambient scheme. -/
def retainedPolynomialSecondAmbient :
    neighborhoodLambdaSite k S (Spec.map (CommRingCat.ofHom f) ≫ b)
      (neighborhoodBaseChangeOpen f (retainedOriginalOpen e U V)) t ⟶
    boundaryBaseAmbientSite k e.base e.toField
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V :=
  (neighborhoodLambdaToAmbient k S (Spec.map (CommRingCat.ofHom f) ≫ b)
      (neighborhoodBaseChangeOpen f (retainedOriginalOpen e U V)) t ≫
    neighborhoodAmbientBaseChange k R b (retainedOriginalOpen e U V) f) ≫
      (retainedPolynomialAmbientSiteIso R b e U V).inv

/-- Both original correction arrows form the exact ambient square needed for
composition on the actual first étale pullback. -/
@[reassoc] theorem retainedPolynomialSecondRestriction_ambient :
    retainedPolynomialSecondRestriction R b e U V f t ≫
      boundaryBaseOpenArrow k e.base e.toField
        (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
        (pullback.snd (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
          (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) e.refinement) U V =
    neighborhoodPencilAlpha k S (Spec.map (CommRingCat.ofHom f) ≫ b)
      (neighborhoodBaseChangeOpen f (retainedOriginalOpen e U V)) t ≫
        retainedPolynomialSecondAmbient R b e U V f t := by
  apply (cancel_mono (retainedPolynomialAmbientSiteIso R b e U V).hom).mp
  have hi : (retainedPolynomialPunctureSiteIso R b e U V).inv ≫
      boundaryBaseOpenArrow k e.base e.toField
        (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
        (pullback.snd (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
          (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) e.refinement) U V ≫
      (retainedPolynomialAmbientSiteIso R b e U V).hom =
        neighborhoodPunctureToAmbient k R b (retainedOriginalOpen e U V) := by
    rw [← retainedPolynomialPunctureSiteIso_ambient, Iso.inv_hom_id_assoc]
  simp only [retainedPolynomialSecondRestriction, retainedPolynomialSecondAmbient,
    Category.assoc, hi, Iso.inv_hom_id, Category.comp_id]
  simpa only [Category.assoc] using
    neighborhoodBaseRestriction_ambient k R b (retainedOriginalOpen e U V) f t

/-- The second ambient map retains the literal original polynomial inclusion. -/
@[reassoc] theorem retainedPolynomialSecondAmbient_original :
    (retainedPolynomialSecondAmbient R b e U V f t).left ≫ retainedToOriginal e U V =
      (neighborhoodSourceOpen S (neighborhoodBaseChangeOpen f
        (retainedOriginalOpen e U V)) t).ι ≫
        (neighborhoodBaseChangeOpen f (retainedOriginalOpen e U V)).ι ≫
          Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) := by
  change (((neighborhoodSourceOpen S (neighborhoodBaseChangeOpen f
      (retainedOriginalOpen e U V)) t).ι ≫
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ∣_
          retainedOriginalOpen e U V)) ≫ (retainedOriginalOpenIso e U V).inv) ≫ _ = _
  simp only [Category.assoc, retainedOriginalOpenIso_inv_original, morphismRestrict_ι]

/-- The entire second marking is the unchanged original zero morphism after
its actual coefficient localization and principal-open restriction. -/
@[reassoc] theorem retainedPolynomialSecondAmbient_zero
    (hzero : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : S)))) ⊆
      neighborhoodBaseChangeOpen f (retainedOriginalOpen e U V)) :
    neighborhoodLambdaZero S (neighborhoodBaseChangeOpen f (retainedOriginalOpen e U V))
        hzero t ≫ (retainedPolynomialSecondAmbient R b e U V f t).left ≫
          retainedToOriginal e U V =
      Scheme.Opens.ι (X := Spec (.of S)) (PrimeSpectrum.basicOpen t) ≫
        Spec.map (CommRingCat.ofHom f) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) := by
  rw [retainedPolynomialSecondAmbient_original, neighborhoodLambdaZero_original_assoc]
  exact congrArg (fun g =>
    Scheme.Opens.ι (X := Spec (.of S)) (PrimeSpectrum.basicOpen t) ≫ g)
      (Scheme.polynomial_zero_scalar_naturality f)

end ScalarMap

/-- From just the retained original zero point, construct the whole-zero base
shrink and the signed second correction on the original first puncture. -/
theorem exists_retainedPolynomial_second_lifting [IsNoetherianRing R]
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (w : Spec (.of R))
    (hw : Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) w ∈
      retainedOriginalOpen e U V) :
    ∃ r : R, w ∈ PrimeSpectrum.basicOpen r ∧
      ∃ hO : IsAffineOpen (neighborhoodBaseChangeOpen
        (algebraMap R (Localization.Away r)) (retainedOriginalOpen e U V)),
      let : IsAffine (neighborhoodBaseChangeOpen
        (algebraMap R (Localization.Away r)) (retainedOriginalOpen e U V)).toScheme := hO
      Set.range (Spec.map (CommRingCat.ofHom
        (Polynomial.evalRingHom (0 : Localization.Away r)))) ⊆
        neighborhoodBaseChangeOpen (algebraMap R (Localization.Away r))
          (retainedOriginalOpen e U V) ∧
      ∃ w' : Spec (.of (Localization.Away r)),
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) w' = w ∧
      ∃ t : Localization.Away r, w' ∈ PrimeSpectrum.basicOpen t ∧
        P.HasRestrictionDifferenceLifting
          (retainedPolynomialSecondRestriction R b e U V
            (algebraMap R (Localization.Away r)) t)
          (neighborhoodPencilBeta k (Localization.Away r)
            (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ b)
            (neighborhoodBaseChangeOpen (algebraMap R (Localization.Away r))
              (retainedOriginalOpen e U V)) t)
          (neighborhoodPencilAlpha k (Localization.Away r)
            (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ b)
            (neighborhoodBaseChangeOpen (algebraMap R (Localization.Away r))
              (retainedOriginalOpen e U V)) t) := by
  obtain ⟨r, hr, hO, hzero, w', hw', t, ht, hL⟩ :=
    P.exists_zeroPoint_original_lifting hP R b (retainedOriginalOpen e U V) w hw
  let : IsAffine (neighborhoodBaseChangeOpen
    (algebraMap R (Localization.Away r)) (retainedOriginalOpen e U V)).toScheme := hO
  refine ⟨r, hr, hO, hzero, w', hw', t, ht, ?_⟩
  exact PresheafWithTransfers.HasRestrictionDifferenceLifting.restrict P hL
    (retainedPolynomialPunctureSiteIso R b e U V).inv

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
