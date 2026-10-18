/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.OriginalPresentationCorrectionSquare
public import Motivic.Cohomology.A1.OriginalPresentationSecondCylinder
public import Motivic.Cohomology.A1.RestrictionDifferenceMarkedComposition

/-! # Affine-enriched original whole-zero correction witnesses

The concrete two-correction construction retains affineness before existential
packaging. Its source is the actual affine fiber product, not an arbitrary
étale neighborhood. The original ambient map and whole retained zero section
are unchanged. Descending two scalar base opens to one original base open is a
separate adapter; no arbitrary extension-open descent is asserted here.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.RelativeProjectiveLine
open Motivic.SmoothSiteAffineCoordinates

universe u

namespace Motivic.SmoothSite

private theorem affineCorrection_a1Map_open
    {k : Type u} [Field k] {B C : SmoothSite (Spec (.of k))}
    (v : B ⟶ C) [IsOpenImmersion v.left] :
    IsOpenImmersion (a1Map (.of k) v).left := by
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstanceAs (IsOpenImmersion v.left))
    (inferInstanceAs (IsOpenImmersion (𝟙 (affineLine (.of k)).left)))
    (MorphismProperty.Over.w v).symm (Category.id_comp _).symm

end Motivic.SmoothSite

namespace Motivic.PresheafWithTransfers

/-- Two signed correction identities assemble on their actual etale pullback,
retaining the original ambient morphism, complete marking and cartesian puncture. -/
private theorem affine_marked_correction_composition
    {k : Type u} [Field k] (P : PresheafWithTransfers.{u + 1} k)
    {O₁ O₂ T₁ T₂ A₁ A₂ B C D Y L : SmoothSite (Spec (.of k))}
    [IsAffine T₁.left] [IsAffine T₂.left] [IsAffine B.left]
    {φ₁ : O₁ ⟶ D} {β₁ : O₁ ⟶ A₁} {α₁ : O₁ ⟶ T₁}
    {φ₂ : O₂ ⟶ A₁} {β₂ : O₂ ⟶ A₂} {α₂ : O₂ ⟶ T₂}
    (h₁ : P.HasRestrictionDifferenceLifting φ₁ β₁ α₁)
    (h₂ : P.HasRestrictionDifferenceLifting φ₂ β₂ α₂)
    (a : A₁ ⟶ B) (p₁ : T₁ ⟶ B) [Etale p₁.left]
    (H₁ : IsPullback β₁ α₁ a p₁)
    (m : T₂ ⟶ B) (hm : φ₂ ≫ a = α₂ ≫ m)
    (j : A₂ ⟶ C) (q₂ : T₂ ⟶ C) [Etale q₂.left]
    (H₂ : IsPullback β₂ α₂ j q₂)
    (p : Y ⟶ L) (η₁ : T₁ ⟶ Y) (b : B.left ⟶ L.left)
    (H₀ : IsPullback p₁.left η₁.left b p.left)
    {K : Scheme.{u}} (i : L.left ⟶ K) (v : C.left ⟶ K)
    (hbase : m.left ≫ b ≫ i = q₂.left ≫ v)
    (ρ : D ⟶ Y) (hρ : φ₁ ≫ ρ = α₁ ≫ η₁)
    {Z : Scheme.{u}} (ζ₂ : Z ⟶ T₂.left) (s : Z ⟶ Y.left) (z : Z ⟶ C.left)
    (hz : ζ₂ ≫ m.left ≫ b = s ≫ p.left) (hζ₂ : ζ₂ ≫ q₂.left = z) :
    ∃ (E : SmoothSite (Spec (.of k))) (η : E ⟶ Y) (q : E ⟶ C) (ζ : Z ⟶ E.left),
      IsAffine E.left ∧ Etale q.left ∧ η.left ≫ p.left ≫ i = q.left ≫ v ∧
      ζ ≫ q.left = z ∧ ζ ≫ η.left = s ∧
      ∃ (O : SmoothSite (Spec (.of k))) (α : O ⟶ E) (β : O ⟶ A₂) (φ : O ⟶ D),
        IsPullback β.left α.left j.left q.left ∧
        φ ≫ ρ = α ≫ η ∧ P.HasRestrictionDifferenceLifting φ β α := by
  obtain ⟨g, α, _hgβ, _hgα, hαfst, _hαsnd, H, hL⟩ :=
    HasRestrictionDifferenceLifting.comp_on_etale_pullback_cartesian
      P h₁ h₂ a p₁ H₁ m hm j q₂ H₂
  let E := SmoothSite.etalePullback p₁ m
  let O := SmoothSite.etalePullback p₁ (φ₂ ≫ a)
  let l := SmoothSite.etalePullbackFst p₁ m
  let n := SmoothSite.etalePullbackSnd p₁ m
  let η : E ⟶ Y := l ≫ η₁
  let q : E ⟶ C := n ≫ q₂
  let β : O ⟶ A₂ := SmoothSite.etalePullbackSnd p₁ (φ₂ ≫ a) ≫ β₂
  let φ := g ≫ φ₁
  let : Etale n.left := by
    change Etale (pullback.snd p₁.left m.left)
    infer_instance
  have hq : Etale q.left := by
    change Etale (n.left ≫ q₂.left)
    infer_instance
  have HE : IsPullback n.left η.left (m.left ≫ b) p.left :=
    (IsPullback.of_hasPullback p₁.left m.left).flip.paste_vert H₀
  let ζ := HE.lift ζ₂ s hz
  have hζn : ζ ≫ n.left = ζ₂ := HE.lift_fst _ _ _
  have hζq : ζ ≫ q.left = z := by
    change ζ ≫ (n.left ≫ q₂.left) = z
    rw [← Category.assoc, hζn, hζ₂]
  refine ⟨E, η, q, ζ, inferInstanceAs (IsAffine (pullback p₁.left m.left)), hq, ?_, hζq,
    HE.lift_snd _ _ _, O, α, β, φ, ?_, ?_, hL⟩
  · calc
      _ = n.left ≫ m.left ≫ b ≫ i := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ i) HE.w.symm
      _ = q.left ≫ v := by rw [hbase]; rfl
  · let : Etale q.left := hq
    have Hq : IsPullback β α j q := H
    exact ((SmoothSite.forgetScheme (Spec (.of k))).map_isPullback Hq.flip).flip
  · change (g ≫ φ₁) ≫ ρ = α ≫ (l ≫ η₁)
    rw [Category.assoc, hρ, ← Category.assoc, ← hαfst, Category.assoc]


end Motivic.PresheafWithTransfers

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

local instance affineCombinedCorrectionTarget : IsAffine e.target := e.target_affine
local instance affineCombinedCorrectionRefinement : IsOpenImmersion e.refinement :=
  e.refinement_open
local instance affineCombinedCorrectionField : Smooth e.toField := e.base_smooth
local instance affineCombinedCorrectionSmooth : SmoothOfRelativeDimension 1
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) := e.target_smooth

/-- Assemble two fixed original corrections without expanding their existential
geometric producers inside the native marked-pullback proof. -/
private theorem exists_scalar_affine_torus_neighborhood_lifting
    [IsAffine (RelativePolynomialOpenSpans.lineSite (k := k) (R := R)).left]
    [IsAffine (RelativePolynomialOpenSpans.openSite
      (k := k) (Polynomial.X : Polynomial R)).left]
    [IsOpenImmersion (RelativePolynomialOpenSpans.openInclusion
      (k := k) (Polynomial.X : Polynomial R)).left]
    (U : e.target.Opens) (V : (Spec e.base).Opens)
    [IsAffine V.toScheme]
    [IsAffine (boundaryBaseSourceOpen
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V).toScheme]
    (P : PresheafWithTransfers.{u + 1} k)
    (s₀ : Spec (.of R) ⟶ Y.left)
    (hs₀ : s₀ ≫ p.left = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))
    (h₁ :
      let a := RelativePolynomialOpenSpans.openInclusion (k := k) (Polynomial.X : Polynomial R)
      let x := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) w
      let Q₁ := retainedCorrectionSquare p a z s x e U V
      P.HasRestrictionDifferenceLifting (retainedOverlapToOriginal p a z s x e U V)
        Q₁.f₁₂ Q₁.f₁₃)
    {S : Type u} [CommRing S] [Algebra k S] [Algebra.Smooth k S]
    (f : R →ₐ[k] S)
    [Smooth (Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      AffineTorusPolynomialPresentation.baseMap k R)]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    [IsAffine (neighborhoodBaseChangeOpen f.toRingHom (retainedOriginalOpen e U V)).toScheme]
    (t : S)
    (hzero : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : S)))) ⊆
      neighborhoodBaseChangeOpen f.toRingHom (retainedOriginalOpen e U V))
    (w' : Spec (.of S)) (hw' : Spec.map (CommRingCat.ofHom f.toRingHom) w' = w)
    (ht : w' ∈ PrimeSpectrum.basicOpen t)
    (h₂ :
      let bS := Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        AffineTorusPolynomialPresentation.baseMap k R
      let O₂ := neighborhoodBaseChangeOpen f.toRingHom (retainedOriginalOpen e U V)
      P.HasRestrictionDifferenceLifting
        (retainedPolynomialSecondRestriction R
          (AffineTorusPolynomialPresentation.baseMap k R) e U V f.toRingHom t)
        (neighborhoodPencilBeta k S bS O₂ t) (neighborhoodPencilAlpha k S bS O₂ t)) :
    ∃ (B : SmoothSite (Spec (.of k)))
      (v : B ⟶ AffineTorusPolynomialPresentation.affineSite k R),
      IsAffine B.left ∧ IsOpenImmersion v.left ∧ w ∈ Set.range v.left ∧
      ∃ (E : SmoothSite (Spec (.of k))) (η : E ⟶ Y)
        (q : E ⟶ SmoothSite.a1Cylinder (.of k) B) (ζ : B.left ⟶ E.left),
        IsAffine E.left ∧ Etale q.left ∧
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
  let a := RelativePolynomialOpenSpans.openInclusion (k := k) (Polynomial.X : Polynomial R)
  let x := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) w
  let : IsAffine (retainedOriginalOpen e U V).toScheme := retainedOriginalOpen_affine e U V
  let bS := Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    AffineTorusPolynomialPresentation.baseMap k R
  let O₂ := neighborhoodBaseChangeOpen f.toRingHom (retainedOriginalOpen e U V)
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
  let : IsOpenImmersion q₂.left :=
    retainedPolynomialSecondCylinder_isOpenImmersion R e U V f t
  change P.HasRestrictionDifferenceLifting φ₁ Q₁.f₁₂ Q₁.f₁₃ at h₁
  have h₂' : P.HasRestrictionDifferenceLifting φ₂ β₂ α₂ :=
    PresheafWithTransfers.HasRestrictionDifferenceLifting.iso_right P h₂ ψ
  have H₂ : IsPullback β₂ α₂ (SmoothSite.contractionOpen (.of k) B) q₂ :=
    neighborhoodCorrection_isPullback k S bS _ O₂ t
  let ζ₂ := neighborhoodLambdaZero S O₂ hzero t
  have hz : ζ₂ ≫ m.left ≫ retainedToOriginal e U V = (v.left ≫ s₀) ≫ p.left := by
    rw [Category.assoc, hs₀]
    exact retainedPolynomialSecondAmbient_zero R
      (AffineTorusPolynomialPresentation.baseMap k R) e U V f.toRingHom t hzero
  let : IsAffine Q₁.X₄.left := inferInstanceAs
    (IsAffine (boundaryBaseSourceOpen
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V).toScheme)
  let : IsAffineHom p.left := isAffineHom_of_isAffine p.left
  let : IsAffine Q₁.X₃.left := IsAffine.of_isIso
    (retainedEtale_original_isPullback p a z s x e U V).isoPullback.hom
  let : IsAffine (neighborhoodLambdaSite k S bS O₂ t).left :=
    neighborhoodSourceOpen_affine S O₂ t
  obtain ⟨E, η, q, ζ, hE, hq, hbase, hζq, hζη, O, α, β, φ, H, hφ, hL⟩ :=
    Motivic.PresheafWithTransfers.affine_marked_correction_composition
      P h₁ h₂' Q₁.f₂₄ Q₁.f₃₄
      (retainedCorrectionSquare_isPullback p a z s x e U V) m
      (retainedPolynomialSecondRestriction_ambient R
        (AffineTorusPolynomialPresentation.baseMap k R) e U V f.toRingHom t)
      (SmoothSite.contractionOpen (.of k) B) q₂ H₂
      p (retainedEtaleToOriginal p a z s x e U V) (retainedToOriginal e U V)
      (retainedEtale_original_isPullback p a z s x e U V)
      (lineCylinderIso (k := k) (R := R)).hom.left
      (SmoothSite.a1Map (.of k) v).left
      (retainedPolynomialSecondCylinder_original R e U V f t).symm
      (SmoothSite.etalePullbackFst p a)
      (retainedOverlapToOriginal_etale p a z s x e U V)
      ζ₂ (v.left ≫ s₀) (SmoothSite.a1Section (.of k) B 0).left hz
      (retainedPolynomialSecondCylinder_zero R e U V f t hzero)
  have hv : IsOpenImmersion v.left := by
    change IsOpenImmersion (Scheme.Opens.ι (X := Spec (.of S)) (PrimeSpectrum.basicOpen t) ≫
      Spec.map (CommRingCat.ofHom f.toRingHom))
    infer_instance
  refine ⟨B, v, inferInstance, hv, ⟨⟨w', ht⟩, hw'⟩, E, η, q, ζ, hE, hq, ?_, hζq,
    hζη, O, α, β, φ, H, hφ, hL⟩
  exact MorphismProperty.Over.Hom.ext hbase

/-- Assemble the second actual correction over a fixed first retained refinement.
This private step keeps the two large geometric existential eliminations separate. -/
private theorem exists_retained_affine_torus_neighborhood_lifting
    [IsAffine (RelativePolynomialOpenSpans.lineSite (k := k) (R := R)).left]
    [IsAffine (RelativePolynomialOpenSpans.openSite
      (k := k) (Polynomial.X : Polynomial R)).left]
    [IsOpenImmersion (RelativePolynomialOpenSpans.openInclusion
      (k := k) (Polynomial.X : Polynomial R)).left]
    (U : e.target.Opens) (V : (Spec e.base).Opens)
    [IsAffine V.toScheme]
    [IsAffine (boundaryBaseSourceOpen
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V).toScheme]
    (hw : Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) w ∈
      retainedOriginalOpen e U V)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (s₀ : Spec (.of R) ⟶ Y.left)
    (hs₀ : s₀ ≫ p.left = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))
    (h₁ :
      let a := RelativePolynomialOpenSpans.openInclusion (k := k) (Polynomial.X : Polynomial R)
      let x := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) w
      let Q₁ := retainedCorrectionSquare p a z s x e U V
      P.HasRestrictionDifferenceLifting (retainedOverlapToOriginal p a z s x e U V)
        Q₁.f₁₂ Q₁.f₁₃) :
    ∃ (B : SmoothSite (Spec (.of k)))
      (v : B ⟶ AffineTorusPolynomialPresentation.affineSite k R),
      IsAffine B.left ∧ IsOpenImmersion v.left ∧ w ∈ Set.range v.left ∧
      ∃ (E : SmoothSite (Spec (.of k))) (η : E ⟶ Y)
        (q : E ⟶ SmoothSite.a1Cylinder (.of k) B) (ζ : B.left ⟶ E.left),
        IsAffine E.left ∧ Etale q.left ∧
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
  let : IsAffine (retainedOriginalOpen e U V).toScheme := retainedOriginalOpen_affine e U V
  obtain ⟨r, _hr, hO, hzero, w', hw', t, ht, h₂⟩ :=
    exists_retainedPolynomial_second_lifting R
      (AffineTorusPolynomialPresentation.baseMap k R) e U V P hP w hw
  let S := Localization.Away r
  let : Algebra.Smooth R S := Algebra.Smooth.of_isLocalization_Away r
  let : Algebra.Smooth k S := Algebra.Smooth.comp k R S
  let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
  let bS := Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    AffineTorusPolynomialPresentation.baseMap k R
  let : Smooth bS := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫
      AffineTorusPolynomialPresentation.baseMap k R)
    infer_instance
  let : IsAffine (neighborhoodBaseChangeOpen f.toRingHom
      (retainedOriginalOpen e U V)).toScheme := hO
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
    change IsOpenImmersion (Spec.map
      (CommRingCat.ofHom (algebraMap R (Localization.Away r))))
    infer_instance
  exact exists_scalar_affine_torus_neighborhood_lifting R p z s w e U V P s₀ hs₀ h₁
    f t hzero w' hw' ht h₂

include e in
/-- From the constructed original presentation and original whole-zero marking,
produce an actual open-base etale neighborhood with a cartesian torus puncture
and the signed lift of every original overlap section. No local image or
correction witness is an input. -/
theorem exists_original_affine_torus_neighborhood_lifting
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (s₀ : Spec (.of R) ⟶ Y.left)
    (hs₀ : s₀ ≫ p.left = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) :
    ∃ (B : SmoothSite (Spec (.of k)))
      (v : B ⟶ AffineTorusPolynomialPresentation.affineSite k R),
      IsAffine B.left ∧ IsOpenImmersion v.left ∧ w ∈ Set.range v.left ∧
      ∃ (E : SmoothSite (Spec (.of k))) (η : E ⟶ Y)
        (q : E ⟶ SmoothSite.a1Cylinder (.of k) B) (ζ : B.left ⟶ E.left),
        IsAffine E.left ∧ Etale η.left ∧ Etale q.left ∧
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
  have hw : x ∈ retainedOriginalOpen e U V := point_mem_retainedOriginalOpen e U V hxU hxV
  obtain ⟨B, v, hB, hv, hwB, E, η, q, ζ, hE, hq, hbase, hζq, hζη, hrest⟩ :=
    exists_retained_affine_torus_neighborhood_lifting R p z s w e U V hw P hP s₀ hs₀ h₁
  let : IsOpenImmersion v.left := hv
  let : Etale q.left := hq
  let : IsOpenImmersion (SmoothSite.a1Map (.of k) v).left :=
    Motivic.SmoothSite.affineCorrection_a1Map_open v
  have hcomp : Etale (η ≫ p ≫ (lineCylinderIso (k := k) (R := R)).hom).left := by
    rw [hbase]
    exact inferInstanceAs (Etale (q.left ≫ (SmoothSite.a1Map (.of k) v).left))
  let : Etale (η.left ≫ (p.left ≫ (lineCylinderIso (k := k) (R := R)).hom.left)) := hcomp
  have hη : Etale η.left := Etale.of_comp η.left
    (p.left ≫ (lineCylinderIso (k := k) (R := R)).hom.left)
  exact ⟨B, v, hB, hv, hwB, E, η, q, ζ, hE, hη, hq, hbase, hζq, hζη, hrest⟩

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
