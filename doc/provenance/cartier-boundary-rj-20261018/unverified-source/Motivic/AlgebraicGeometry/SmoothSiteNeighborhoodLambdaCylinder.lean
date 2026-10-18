/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodOriginalAmbientMaps
public import Motivic.AlgebraicGeometry.SmoothSiteFixedPsiTorus
public import Motivic.Aglib.AlgebraicGeometry.AffineLineZeroNeighborhoodBaseShrink

/-! # The original lambda correction over its actual retained cylinder

The ambient map and the whole-zero marking are literal polynomial morphisms.
The base principal open is the same one as for the psi torus, with no independent
choice or alteration of the original section coordinate.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.RelativeProjectiveLine

variable (k R : Type u) [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme] (r : R)

/-- The original lambda source maps into the whole cylinder over precisely D(r). -/
def neighborhoodLambdaToCylinder :
    neighborhoodLambdaSite k R (AffineTorusPolynomialPresentation.baseMap k R) V r ⟶
      SmoothSite.a1Cylinder (.of k) (fixedPsiBaseSite R r k) :=
  SmoothSite.homMk
    (pullback.lift (neighborhoodProjection R V ∣_ PrimeSpectrum.basicOpen r)
      ((neighborhoodSourceOpen R V r).ι ≫ V.ι ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k R)))) (by
          change (neighborhoodProjection R V ∣_ PrimeSpectrum.basicOpen r) ≫
              (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫
                AffineTorusPolynomialPresentation.baseMap k R) =
            ((neighborhoodSourceOpen R V r).ι ≫ V.ι ≫
              Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k R)))) ≫
                polynomialProjection (.of k)
          simp only [Category.assoc, morphismRestrict_ι_assoc]
          change (neighborhoodSourceOpen R V r).ι ≫
              neighborhoodProjection R V ≫ AffineTorusPolynomialPresentation.baseMap k R =
            (neighborhoodSourceOpen R V r).ι ≫ V.ι ≫
              Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k R))) ≫
                Scheme.Hom.boundaryLineProjection k
          rw [polynomial_scalar_projection]
          change (neighborhoodSourceOpen R V r).ι ≫ neighborhoodProjection R V ≫
              AffineTorusPolynomialPresentation.baseMap k R =
            (neighborhoodSourceOpen R V r).ι ≫ V.ι ≫
              Scheme.Hom.boundaryLineProjection R ≫
                AffineTorusPolynomialPresentation.baseMap k R
          simpa only [Category.assoc] using congrArg
            (fun f => (neighborhoodSourceOpen R V r).ι ≫ f ≫
              AffineTorusPolynomialPresentation.baseMap k R)
            (neighborhoodProjection_eq R V))) (by
      change (pullback.lift _ _ _ ≫ (pullback.fst _ _ ≫ _)) =
        ((neighborhoodSourceOpen R V r).ι ≫ neighborhoodProjection R V) ≫ _
      rw [pullback.lift_fst_assoc]
      change (neighborhoodProjection R V ∣_ PrimeSpectrum.basicOpen r) ≫
          (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫
            AffineTorusPolynomialPresentation.baseMap k R) = _
      rw [morphismRestrict_ι_assoc]
      rfl)

/-- The original projection onto D(r) is unchanged. -/
@[reassoc] theorem neighborhoodLambdaToCylinder_projection :
    (neighborhoodLambdaToCylinder k R V r).left ≫
      (SmoothSite.a1Projection (.of k) (fixedPsiBaseSite R r k)).left =
        neighborhoodProjection R V ∣_ PrimeSpectrum.basicOpen r := by
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

/-- The original affine coordinate is unchanged. -/
@[reassoc] theorem neighborhoodLambdaToCylinder_parameter :
    (neighborhoodLambdaToCylinder k R V r).left ≫
      (SmoothSite.productSnd (fixedPsiBaseSite R r k) (SmoothSite.affineLine (.of k))).left =
      (neighborhoodSourceOpen R V r).ι ≫ V.ι ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k R))) := by
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  exact pullback.lift_snd _ _ _

/-- Mapping the retained cylinder back to the original one is exactly the
original open inclusion in the polynomial chart. -/
@[reassoc] theorem neighborhoodLambdaToCylinder_original :
    (neighborhoodLambdaToCylinder k R V r).left ≫
      (SmoothSite.a1Map (.of k) (SmoothSite.openInclusion
        (AffineTorusPolynomialPresentation.affineSite k R) (PrimeSpectrum.basicOpen r))).left =
      (neighborhoodSourceOpen R V r).ι ≫ V.ι ≫
        (PolynomialOpenQuotient.ambientIso (algebraMap k R)).hom := by
  change (show (neighborhoodSourceOpen R V r).toScheme ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))
        (polynomialProjection (.of k)) from
      (neighborhoodLambdaToCylinder k R V r).left ≫
        (SmoothSite.a1Map (.of k) (SmoothSite.openInclusion
          (AffineTorusPolynomialPresentation.affineSite k R) (PrimeSpectrum.basicOpen r))).left) =
    (neighborhoodSourceOpen R V r).ι ≫ V.ι ≫
      (PolynomialOpenQuotient.ambientIso (algebraMap k R)).hom
  apply pullback.hom_ext
  · have h := congrArg (fun f => f.left)
      (SmoothSite.a1Map_projection (.of k) (SmoothSite.openInclusion
        (AffineTorusPolynomialPresentation.affineSite k R) (PrimeSpectrum.basicOpen r)))
    change (SmoothSite.a1Map (.of k) (SmoothSite.openInclusion
        (AffineTorusPolynomialPresentation.affineSite k R) (PrimeSpectrum.basicOpen r))).left ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R)))
          (polynomialProjection (.of k)) =
      pullback.fst (fixedPsiBaseSite R r k).hom (polynomialProjection (.of k)) ≫
        Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) at h
    have hp := neighborhoodLambdaToCylinder_projection k R V r
    change (neighborhoodLambdaToCylinder k R V r).left ≫
      pullback.fst (fixedPsiBaseSite R r k).hom (polynomialProjection (.of k)) =
        neighborhoodProjection R V ∣_ PrimeSpectrum.basicOpen r at hp
    simp only [Category.assoc, h, reassoc_of% hp,
      morphismRestrict_ι, PolynomialOpenQuotient.ambientIso_fst]
    change (neighborhoodSourceOpen R V r).ι ≫ neighborhoodProjection R V =
      (neighborhoodSourceOpen R V r).ι ≫ V.ι ≫ Scheme.Hom.boundaryLineProjection R
    exact congrArg (fun f => (neighborhoodSourceOpen R V r).ι ≫ f)
      (neighborhoodProjection_eq R V)
  · have h := congrArg (fun f => f.left)
      (SmoothSite.productMap_snd (SmoothSite.openInclusion
        (AffineTorusPolynomialPresentation.affineSite k R) (PrimeSpectrum.basicOpen r))
        (𝟙 (SmoothSite.affineLine (.of k))))
    change (SmoothSite.a1Map (.of k) (SmoothSite.openInclusion
        (AffineTorusPolynomialPresentation.affineSite k R) (PrimeSpectrum.basicOpen r))).left ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k R)))
          (polynomialProjection (.of k)) =
      pullback.snd (fixedPsiBaseSite R r k).hom (polynomialProjection (.of k)) ≫
        𝟙 (Spec (.of (Polynomial k))) at h
    simp only [Category.comp_id] at h
    have hp := neighborhoodLambdaToCylinder_parameter k R V r
    change (neighborhoodLambdaToCylinder k R V r).left ≫
      pullback.snd (fixedPsiBaseSite R r k).hom (polynomialProjection (.of k)) = _ at hp
    simp only [Category.assoc, h, hp, PolynomialOpenQuotient.ambientIso_snd]

/-- The correction source is an actual open in its retained whole cylinder. -/
instance neighborhoodLambdaToCylinder_isOpenImmersion :
    IsOpenImmersion (neighborhoodLambdaToCylinder k R V r).left := by
  let i := (SmoothSite.a1Map (.of k) (SmoothSite.openInclusion
    (AffineTorusPolynomialPresentation.affineSite k R) (PrimeSpectrum.basicOpen r))).left
  let : IsOpenImmersion i := fixedPsiBaseOpen_a1Map_isOpenImmersion R r k
  have : IsOpenImmersion ((neighborhoodLambdaToCylinder k R V r).left ≫ i) := by
    change IsOpenImmersion ((neighborhoodLambdaToCylinder k R V r).left ≫
      (SmoothSite.a1Map (.of k) (SmoothSite.openInclusion
        (AffineTorusPolynomialPresentation.affineSite k R) (PrimeSpectrum.basicOpen r))).left)
    rw [neighborhoodLambdaToCylinder_original]
    infer_instance
  exact IsOpenImmersion.of_comp _ i

/-- The common source is the actual puncture of the retained lambda cylinder.
The comparison preserves both original arrows, not only their underlying opens. -/
theorem neighborhoodLambdaPuncture_isPullback :
    IsPullback
      ((neighborhoodPencilBeta k R (AffineTorusPolynomialPresentation.baseMap k R) V r).left ≫
        (neighborhoodPsiTorusIso R r k).hom.left)
      (neighborhoodPencilAlpha k R (AffineTorusPolynomialPresentation.baseMap k R) V r).left
      (SmoothSite.contractionOpen (.of k) (fixedPsiBaseSite R r k)).left
      (neighborhoodLambdaToCylinder k R V r).left := by
  let e := neighborhoodPsiTorusIso R r k
  let eψ := (SmoothSite.forgetScheme (Spec (.of k))).mapIso e
  let i := (SmoothSite.a1Map (.of k) (SmoothSite.openInclusion
    (AffineTorusPolynomialPresentation.affineSite k R) (PrimeSpectrum.basicOpen r))).left
  let a := (SmoothSite.contractionOpen (.of k) (fixedPsiBaseSite R r k)).left
  let q := (neighborhoodLambdaToCylinder k R V r).left
  let β := (neighborhoodPencilBeta k R
    (AffineTorusPolynomialPresentation.baseMap k R) V r).left ≫ e.hom.left
  let α := (neighborhoodPencilAlpha k R
    (AffineTorusPolynomialPresentation.baseMap k R) V r).left
  have H : IsPullback β α (a ≫ i) (q ≫ i) := by
    apply (commonNeighborhoodPuncture_isPullback R V r).of_iso
      (Iso.refl _) eψ (Iso.refl _) (PolynomialOpenQuotient.ambientIso (algebraMap k R))
    · simp only [Iso.refl_hom, Category.id_comp]
      rfl
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · exact (neighborhoodPsiTorusIso_affine R r k).symm
    · exact (neighborhoodLambdaToCylinder_original k R V r).symm
  let : IsOpenImmersion i := fixedPsiBaseOpen_a1Map_isOpenImmersion R r k
  have h : β ≫ a = α ≫ q := by
    apply (cancel_mono i).mp
    simpa only [Category.assoc] using H.w
  have H' : IsPullback β (α ≫ 𝟙 _) (a ≫ i) (q ≫ i) := by
    simpa only [Category.comp_id] using H
  exact H'.of_bot h (IsPullback.of_vert_isIso_mono ⟨by
    change (𝟙 _) ≫ (q ≫ i) = q ≫ i
    exact Category.id_comp _⟩)

/-- The entire lambda marking maps to the literal zero section of the retained
cylinder, not merely to its underlying zero locus. -/
@[reassoc] theorem neighborhoodLambdaZero_cylinder
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V) :
    neighborhoodLambdaZero R V hV r ≫ (neighborhoodLambdaToCylinder k R V r).left =
      (SmoothSite.a1Section (.of k) (fixedPsiBaseSite R r k) 0).left := by
  change (show Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ⟶
      pullback (fixedPsiBaseSite R r k).hom (polynomialProjection (.of k)) from
      neighborhoodLambdaZero R V hV r ≫ (neighborhoodLambdaToCylinder k R V r).left) =
    (show Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ⟶
      pullback (fixedPsiBaseSite R r k).hom (polynomialProjection (.of k)) from
      (SmoothSite.a1Section (.of k) (fixedPsiBaseSite R r k) 0).left)
  apply pullback.hom_ext
  · have hs := congrArg (fun f => f.left)
      (SmoothSite.a1Section_projection (.of k) (fixedPsiBaseSite R r k) 0)
    change (SmoothSite.a1Section (.of k) (fixedPsiBaseSite R r k) 0).left ≫
      pullback.fst (fixedPsiBaseSite R r k).hom (polynomialProjection (.of k)) =
        𝟙 ((fixedPsiBaseSite R r k).left) at hs
    have hp := neighborhoodLambdaToCylinder_projection k R V r
    change (neighborhoodLambdaToCylinder k R V r).left ≫
      pullback.fst (fixedPsiBaseSite R r k).hom (polynomialProjection (.of k)) = _ at hp
    rw [Category.assoc, hp, hs]
    apply (cancel_mono
      (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r))).mp
    rw [Category.assoc, morphismRestrict_ι]
    change neighborhoodLambdaZero R V hV r ≫
        (neighborhoodSourceOpen R V r).ι ≫ neighborhoodProjection R V =
      (𝟙 ((fixedPsiBaseSite R r k).left)) ≫
        Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r)
    rw [neighborhoodLambdaZero_ι_assoc, neighborhoodZero_projection,
      Category.comp_id, Category.id_comp]
  · have hs : (SmoothSite.a1Section (.of k) (fixedPsiBaseSite R r k) 0).left ≫
        pullback.snd (fixedPsiBaseSite R r k).hom (polynomialProjection (.of k)) =
      (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫
        AffineTorusPolynomialPresentation.baseMap k R) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) :=
      pullback.lift_snd _ _ _
    have hp := neighborhoodLambdaToCylinder_parameter k R V r
    change (neighborhoodLambdaToCylinder k R V r).left ≫
      pullback.snd (fixedPsiBaseSite R r k).hom (polynomialProjection (.of k)) = _ at hp
    rw [Category.assoc, hp, hs, neighborhoodLambdaZero_original_assoc]
    have he : Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k R))) =
      AffineTorusPolynomialPresentation.baseMap k R ≫
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) :=
      Scheme.polynomial_zero_scalar_naturality (algebraMap k R)
    simpa only [Category.assoc] using congrArg
      (fun f => Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫ f) he

end AlgebraicGeometry.RelativeProjectiveLine
