/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.OriginalPresentationCorrectionSquare
public import Motivic.Cohomology.A1.OriginalPresentationSecondCylinder
public import Motivic.Cohomology.A1.RestrictionDifferenceCartesianComposition

/-! # The two original corrections on one actual whole-zero etale neighborhood

Both signed lifts are constructed from homotopy invariance. Their ambient terms
are added on the actual etale pullback, while the selected point, original open
base arrow, original section, and complete zero marking are retained.
-/

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
  {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]
  (p : Y ⟶ RelativePolynomialOpenSpans.lineSite (k := k) (R := R)) [Etale p.left]
  {Z : Scheme.{u}} (z : Z ⟶ Spec (.of (Polynomial R))) (s : Z ⟶ Y.left)
  (w : Spec (.of R))
  (e : OriginalEtalePresentation k
    (boundaryLineProjection R ≫ AffineTorusPolynomialPresentation.baseMap k R) p.left
    (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) z s
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) w))

local instance combinedCorrectionTarget : IsAffine e.target := e.target_affine
local instance combinedCorrectionRefinement : IsOpenImmersion e.refinement := e.refinement_open
local instance combinedCorrectionField : Smooth e.toField := e.base_smooth
local instance combinedCorrectionSmooth : SmoothOfRelativeDimension 1
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) := e.target_smooth

include e in
/-- From the constructed original presentation and original whole-zero marking,
produce an actual open-base etale neighborhood with a cartesian torus puncture
and the signed lift of every original overlap section. No local image or
correction witness is an input. -/
theorem exists_original_torus_neighborhood_lifting
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (s₀ : Spec (.of R) ⟶ Y.left)
    (hs₀ : s₀ ≫ p.left = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) :
    ∃ (B : SmoothSite (Spec (.of k)))
      (v : B ⟶ AffineTorusPolynomialPresentation.affineSite k R),
      IsOpenImmersion v.left ∧ w ∈ Set.range v.left ∧
      ∃ (E : SmoothSite (Spec (.of k))) (η : E ⟶ Y)
        (q : E ⟶ SmoothSite.a1Cylinder (.of k) B) (ζ : B.left ⟶ E.left),
        Etale q.left ∧
        η ≫ p ≫ (lineCylinderIso (k := k) (R := R)).hom =
          q ≫ SmoothSite.a1Map (.of k) v ∧
        ζ ≫ q.left = (SmoothSite.a1Section (.of k) B 0).left ∧
        ζ ≫ η.left = v.left ≫ s₀ ∧
        ∃ (O : SmoothSite (Spec (.of k))) (α : O ⟶ E)
          (β : O ⟶ SmoothSite.torusCylinder (.of k) B)
          (φ : O ⟶ SmoothSite.etalePullback p
            (RelativePolynomialOpenSpans.openInclusion (k := k) (Polynomial.X : Polynomial R))),
          IsPullback β.left α.left (SmoothSite.contractionOpen (.of k) B).left q.left ∧
          φ ≫ SmoothSite.etalePullbackFst p
            (RelativePolynomialOpenSpans.openInclusion (k := k) (Polynomial.X : Polynomial R)) =
              α ≫ η ∧ P.HasRestrictionDifferenceLifting φ β α := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let : IsAffine (RelativePolynomialOpenSpans.lineSite (k := k) (R := R)).left :=
    inferInstanceAs (IsAffine (Spec (.of (Polynomial R))))
  let a := RelativePolynomialOpenSpans.openInclusion (k := k) (Polynomial.X : Polynomial R)
  let : IsAffine (RelativePolynomialOpenSpans.openSite
      (k := k) (Polynomial.X : Polynomial R)).left := by
    change IsAffine (Scheme.Opens.toScheme (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R)))
    exact IsAffineOpen.Spec_basicOpen _
  let : IsOpenImmersion a.left := by
    change IsOpenImmersion (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R)))
    infer_instance
  let x := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) w
  obtain ⟨U, _hU, hxU, V, hV, hxV, _hc, hW, h₁⟩ :=
    exists_original_overlap_lifting p a z s x e P hP
  let : IsAffine V.toScheme := hV
  let : IsAffine (boundaryBaseSourceOpen
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V).toScheme := hW
  let : IsAffine (retainedOriginalOpen e U V).toScheme := retainedOriginalOpen_affine e U V
  have hw : x ∈ retainedOriginalOpen e U V := point_mem_retainedOriginalOpen e U V hxU hxV
  obtain ⟨r, _hr, hO, hzero, w', hw', t, ht, h₂⟩ :=
    exists_retainedPolynomial_second_lifting R
      (AffineTorusPolynomialPresentation.baseMap k R) e U V P hP w hw
  let S := Localization.Away r
  let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
  let bS := Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    AffineTorusPolynomialPresentation.baseMap k R
  let O₂ := neighborhoodBaseChangeOpen f.toRingHom (retainedOriginalOpen e U V)
  let : IsAffine O₂.toScheme := hO
  let Q₁ := retainedCorrectionSquare p a z s x e U V
  let φ₁ := retainedOverlapToOriginal p a z s x e U V
  let φ₂ := retainedPolynomialSecondRestriction R
    (AffineTorusPolynomialPresentation.baseMap k R) e U V f.toRingHom t
  let α₂ := neighborhoodPencilAlpha k S bS O₂ t
  let ψ := neighborhoodPsiTorusIsoOfBaseEq k S bS
    (MorphismProperty.Over.w (AffineTorusPolynomialPresentation.affineMorphism f)) t
  let β₂ := neighborhoodPencilBeta k S bS O₂ t ≫ ψ.hom
  let m := retainedPolynomialSecondAmbient R
    (AffineTorusPolynomialPresentation.baseMap k R) e U V f.toRingHom t
  let B := fixedPsiBaseSite S t k
  let v : B ⟶ AffineTorusPolynomialPresentation.affineSite k R :=
    retainedPolynomialSecondBase R f t
  let q₂ := retainedPolynomialSecondCylinder R e U V f t
  change P.HasRestrictionDifferenceLifting φ₁ Q₁.f₁₂ Q₁.f₁₃ at h₁
  have h₂' : P.HasRestrictionDifferenceLifting φ₂ β₂ α₂ :=
    PresheafWithTransfers.HasRestrictionDifferenceLifting.iso_right P h₂ ψ
  have H₂ : IsPullback β₂ α₂ (SmoothSite.contractionOpen (.of k) B) q₂ :=
    neighborhoodCorrection_isPullback k S bS _ O₂ t
  obtain ⟨g, α, _hgβ, _hgα, hαfst, _hαsnd, H, hL⟩ :=
    PresheafWithTransfers.HasRestrictionDifferenceLifting.comp_on_etale_pullback_cartesian
      P h₁ h₂' Q₁.f₂₄ Q₁.f₃₄
      (retainedCorrectionSquare_isPullback p a z s x e U V) m
      (retainedPolynomialSecondRestriction_ambient R
        (AffineTorusPolynomialPresentation.baseMap k R) e U V f.toRingHom t)
      (SmoothSite.contractionOpen (.of k) B) q₂ H₂
  let E := SmoothSite.etalePullback Q₁.f₃₄ m
  let O := SmoothSite.etalePullback Q₁.f₃₄ (φ₂ ≫ Q₁.f₂₄)
  let l := SmoothSite.etalePullbackFst Q₁.f₃₄ m
  let n := SmoothSite.etalePullbackSnd Q₁.f₃₄ m
  let η : E ⟶ Y := l ≫ retainedEtaleToOriginal p a z s x e U V
  let q : E ⟶ SmoothSite.a1Cylinder (.of k) B := n ≫ q₂
  let β : O ⟶ SmoothSite.torusCylinder (.of k) B :=
    SmoothSite.etalePullbackSnd Q₁.f₃₄ (φ₂ ≫ Q₁.f₂₄) ≫ β₂
  let φ := g ≫ φ₁
  have hq : Etale q.left := by
    change Etale (n.left ≫ q₂.left)
    infer_instance
  have HE : IsPullback n.left η.left (m.left ≫ retainedToOriginal e U V) p.left := by
    exact (IsPullback.of_hasPullback Q₁.f₃₄.left m.left).flip.paste_vert
      (retainedEtale_original_isPullback p a z s x e U V)
  let ζ₂ := neighborhoodLambdaZero S O₂ hzero t
  have hz : ζ₂ ≫ (m.left ≫ retainedToOriginal e U V) = (v.left ≫ s₀) ≫ p.left := by
    rw [Category.assoc, hs₀]
    exact retainedPolynomialSecondAmbient_zero R
      (AffineTorusPolynomialPresentation.baseMap k R) e U V f.toRingHom t hzero
  let ζ := HE.lift ζ₂ (v.left ≫ s₀) hz
  have hζn : ζ ≫ n.left = ζ₂ := HE.lift_fst _ _ _
  have hζq : ζ ≫ q.left = (SmoothSite.a1Section (.of k) B 0).left := by
    change ζ ≫ (n.left ≫ q₂.left) = _
    rw [← Category.assoc, hζn]
    exact retainedPolynomialSecondCylinder_zero R e U V f t hzero
  have hv : IsOpenImmersion v.left := by
    change IsOpenImmersion (Scheme.Opens.ι (X := Spec (.of S)) (PrimeSpectrum.basicOpen t) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)))
    infer_instance
  refine ⟨B, v, hv, ⟨⟨w', ht⟩, hw'⟩, E, η, q, ζ, hq, ?_, hζq,
    HE.lift_snd _ _ _, O, α, β, φ, ?_, ?_, hL⟩
  · apply MorphismProperty.Over.Hom.ext
    change (η.left ≫ p.left) ≫ (lineCylinderIso (k := k) (R := R)).hom.left =
      (n.left ≫ q₂.left) ≫ (SmoothSite.a1Map (.of k) v).left
    rw [← HE.w]
    simpa only [Category.assoc] using congrArg (fun h => n.left ≫ h)
      (retainedPolynomialSecondCylinder_original R e U V f t).symm
  · let : Etale q.left := hq
    exact (SmoothSite.forgetScheme (Spec (.of k))).map_isPullback H
  · change (g ≫ φ₁) ≫ SmoothSite.etalePullbackFst p a = α ≫ (l ≫ _)
    rw [Category.assoc, retainedOverlapToOriginal_etale, ← Category.assoc,
      ← hαfst, Category.assoc]

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
