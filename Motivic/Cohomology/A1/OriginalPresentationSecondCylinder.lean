/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.OriginalPresentationSecondCorrection
public import Motivic.Cohomology.A1.NeighborhoodCorrectionCoordinates

/-! # The actual second correction over its original coefficient cylinder -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.RelativeProjectiveLine
open Motivic.SmoothSiteAffineCoordinates

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation

variable {k : Type u} [Field k] (R : Type u) [CommRing R]
  [Algebra k R] [Algebra.Smooth k R]
  {Y Z : Scheme.{u}} {p : Y ⟶ Spec (.of (Polynomial R))}
  {z : Z ⟶ Spec (.of (Polynomial R))} {s : Z ⟶ Y}
  {x : Spec (.of (Polynomial R))}
  (e : OriginalEtalePresentation k
    (boundaryLineProjection R ≫ AffineTorusPolynomialPresentation.baseMap k R) p
    (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) z s x)

local instance secondCylinderTarget : IsAffine e.target := e.target_affine
local instance secondCylinderRefinement : IsOpenImmersion e.refinement := e.refinement_open
local instance secondCylinderField : Smooth e.toField := e.base_smooth
local instance secondCylinderSmooth : SmoothOfRelativeDimension 1
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) := e.target_smooth

variable (U : e.target.Opens) (V : (Spec e.base).Opens)
  [IsAffine V.toScheme]
  [IsAffine (boundaryBaseSourceOpen
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V).toScheme]

local instance secondCylinderRetainedAffine : IsAffine (retainedOriginalOpen e U V).toScheme :=
  retainedOriginalOpen_affine e U V

variable {S : Type u} [CommRing S] [Algebra k S] [Algebra.Smooth k S] (f : R →ₐ[k] S)
  [Smooth (Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    AffineTorusPolynomialPresentation.baseMap k R)]
  [IsAffine (neighborhoodBaseChangeOpen f.toRingHom (retainedOriginalOpen e U V)).toScheme]
  (t : S)

/-- The base is exactly the retained principal open followed by the original coefficient map. -/
def retainedPolynomialSecondBase : fixedPsiBaseSite S t k ⟶
    AffineTorusPolynomialPresentation.affineSite k R :=
  SmoothSite.openInclusion (AffineTorusPolynomialPresentation.affineSite k S)
    (PrimeSpectrum.basicOpen t) ≫ AffineTorusPolynomialPresentation.affineMorphism f

/-- The actual lambda correction maps to the cylinder over that same retained base. -/
def retainedPolynomialSecondCylinder :
    neighborhoodLambdaSite k S
      (Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        AffineTorusPolynomialPresentation.baseMap k R)
      (neighborhoodBaseChangeOpen f.toRingHom (retainedOriginalOpen e U V)) t ⟶
        SmoothSite.a1Cylinder (.of k) (fixedPsiBaseSite S t k) :=
  neighborhoodLambdaToCylinderOfBaseEq k S
    (Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      AffineTorusPolynomialPresentation.baseMap k R)
    (MorphismProperty.Over.w (AffineTorusPolynomialPresentation.affineMorphism f)) _ t

/-- This map is an actual open in the whole retained cylinder. -/
instance retainedPolynomialSecondCylinder_isOpenImmersion :
    IsOpenImmersion (retainedPolynomialSecondCylinder R e U V f t).left := by
  unfold retainedPolynomialSecondCylinder
  infer_instance

/-- The entire ambient square is the original polynomial square, with its unchanged coordinate. -/
@[reassoc] theorem retainedPolynomialSecondCylinder_original :
    (retainedPolynomialSecondCylinder R e U V f t).left ≫
      (SmoothSite.a1Map (.of k) (retainedPolynomialSecondBase R f t)).left =
    (retainedPolynomialSecondAmbient R (AffineTorusPolynomialPresentation.baseMap k R)
      e U V f.toRingHom t).left ≫ retainedToOriginal e U V ≫
        (lineCylinderIso (k := k) (R := R)).hom.left := by
  calc
    _ = (neighborhoodSourceOpen S (neighborhoodBaseChangeOpen f.toRingHom
          (retainedOriginalOpen e U V)) t).ι ≫
        (neighborhoodBaseChangeOpen f.toRingHom (retainedOriginalOpen e U V)).ι ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f.toRingHom)) ≫
        (lineCylinderIso (k := k) (R := R)).hom.left :=
      neighborhoodLambdaToCylinderOfBaseEq_scalar k S _ _ _ t R f
    _ = _ := (retainedPolynomialSecondAmbient_original_assoc R
      (AffineTorusPolynomialPresentation.baseMap k R) e U V f.toRingHom t
        (lineCylinderIso (k := k) (R := R)).hom.left).symm

omit [IsAffine V.toScheme]
    [IsAffine (boundaryBaseSourceOpen
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V).toScheme] in
/-- The second correction retains the entire literal zero marking of its actual base. -/
@[reassoc] theorem retainedPolynomialSecondCylinder_zero
    (hzero : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : S)))) ⊆
      neighborhoodBaseChangeOpen f.toRingHom (retainedOriginalOpen e U V)) :
    neighborhoodLambdaZero S
      (neighborhoodBaseChangeOpen f.toRingHom (retainedOriginalOpen e U V)) hzero t ≫
        (retainedPolynomialSecondCylinder R e U V f t).left =
      (SmoothSite.a1Section (.of k) (fixedPsiBaseSite S t k) 0).left :=
  neighborhoodLambdaZero_cylinderOfBaseEq k S
    (Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      AffineTorusPolynomialPresentation.baseMap k R)
    (MorphismProperty.Over.w (AffineTorusPolynomialPresentation.affineMorphism f)) _ t hzero

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
