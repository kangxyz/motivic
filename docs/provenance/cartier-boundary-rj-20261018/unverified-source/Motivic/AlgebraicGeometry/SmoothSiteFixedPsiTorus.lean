/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodPencilSites
public import Motivic.AlgebraicGeometry.Correspondences.AffineTorusPolynomialBaseChange
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.ContractionGeometry
public import Motivic.Aglib.AlgebraicGeometry.PolynomialQuotientCoordinates
public import Motivic.AlgebraicGeometry.SmoothSiteAffineLineOpenMaps

/-! # The fixed psi source is the literal torus over its original base open

The only shrink is the specified principal open of the original base. The
comparison retains the original affine inclusion and first projection, rather
than replacing the open by an unspecified isomorphic scheme.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.RelativeProjectiveLine

variable (R : Type u) [CommRing R] (r : R)

/-- The literal Laurent open obtained by restricting just the original base. -/
abbrev fixedPsiLaurentOpen : (Spec (.of (LaurentPolynomial R))).Opens :=
  laurentProjection (.of R) ⁻¹ᵁ PrimeSpectrum.basicOpen r

/-- The original polynomial psi open and its Laurent base restriction have the same image. -/
theorem fixedPsiLaurentOpen_range :
    Set.range (fixedPsiSource R r).ι =
      Set.range ((fixedPsiLaurentOpen R r).ι ≫ laurentPlus (.of R)) := by
  have hL (x : Spec (.of (Polynomial R))) :
      x ∈ Set.range (laurentPlus (.of R)) ↔
        x ∈ PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) := by
    rw [← Scheme.Hom.coe_opensRange, laurentPlus_opensRange]
    rfl
  rw [Scheme.Opens.range_ι]
  ext x
  change x ∈ fixedPsiSource R r ↔ _
  rw [fixedPsiSource_eq]
  constructor
  · rintro ⟨hxX, hxr⟩
    obtain ⟨y, hy⟩ := (hL x).mpr hxX
    refine ⟨⟨y, ?_⟩, hy⟩
    change laurentProjection (.of R) y ∈ PrimeSpectrum.basicOpen r
    have hp := congrArg (fun f => f y) (laurentPlus_projection (.of R))
    change polynomialProjection (.of R) (laurentPlus (.of R) y) =
      laurentProjection (.of R) y at hp
    rw [← hp, hy]
    exact hxr
  · rintro ⟨y, rfl⟩
    constructor
    · exact (hL _).mp ⟨y.val, rfl⟩
    · change polynomialProjection (.of R) (laurentPlus (.of R) y.val) ∈
        PrimeSpectrum.basicOpen r
      have hp := congrArg (fun f => f y.val) (laurentPlus_projection (.of R))
      change polynomialProjection (.of R) (laurentPlus (.of R) y.val) =
        laurentProjection (.of R) y.val at hp
      rw [hp]
      exact y.property

/-- The fixed original polynomial open is its actual Laurent base restriction. -/
def fixedPsiLaurentOpenIso :
    (fixedPsiSource R r).toScheme ≅ (fixedPsiLaurentOpen R r).toScheme :=
  IsOpenImmersion.isoOfRangeEq _ _ (fixedPsiLaurentOpen_range R r)

/-- The canonical open comparison preserves the original affine inclusion. -/
@[reassoc (attr := simp)] theorem fixedPsiLaurentOpenIso_ι :
    (fixedPsiLaurentOpenIso R r).hom ≫ (fixedPsiLaurentOpen R r).ι ≫
      laurentPlus (.of R) = (fixedPsiSource R r).ι := by
  simpa only [fixedPsiLaurentOpenIso, Category.assoc] using
    IsOpenImmersion.isoOfRangeEq_hom_fac (fixedPsiSource R r).ι
      ((fixedPsiLaurentOpen R r).ι ≫ laurentPlus (.of R)) (fixedPsiLaurentOpen_range R r)

/-- The canonical open comparison preserves the original coefficient projection. -/
@[reassoc] theorem fixedPsiLaurentOpenIso_projection :
    (fixedPsiLaurentOpenIso R r).hom ≫ (fixedPsiLaurentOpen R r).ι ≫
      laurentProjection (.of R) = fixedPsiProjection R r := by
  change (fixedPsiLaurentOpenIso R r).hom ≫ (fixedPsiLaurentOpen R r).ι ≫
    laurentProjection (.of R) = (fixedPsiSource R r).ι ≫ polynomialProjection (.of R)
  simpa only [Category.assoc, laurentPlus_projection] using
    congrArg (fun f => f ≫ polynomialProjection (.of R)) (fixedPsiLaurentOpenIso_ι R r)

variable (k : Type u) [Field k] [Algebra k R] [Algebra.Smooth k R]

/-- The actual original principal base open as a smooth object. -/
def fixedPsiBaseSite : SmoothSite (Spec (.of k)) :=
  (SmoothSite.opensFunctor (AffineTorusPolynomialPresentation.affineSite k R)).obj
    (PrimeSpectrum.basicOpen r)

instance fixedPsiBaseSite_affine : IsAffine (fixedPsiBaseSite R r k).left := by
  change IsAffine (Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen r))
  exact IsAffineOpen.Spec_basicOpen (R := .of R) r

/-- The literal cylinder map induced by the original principal base open is
an open immersion, through the checked whole-line base-open coordinates. -/
theorem fixedPsiBaseOpen_a1Map_isOpenImmersion :
    IsOpenImmersion (SmoothSite.a1Map (.of k) (SmoothSite.openInclusion
      (AffineTorusPolynomialPresentation.affineSite k R) (PrimeSpectrum.basicOpen r))).left := by
  have h := (SmoothSiteAffineCoordinates.lineBaseOpenCylinderIso
    (k := k) (PrimeSpectrum.basicOpen r)).eq_inv_comp.mpr
      (SmoothSiteAffineCoordinates.lineBaseOpenCylinderIso_comp
        (k := k) (PrimeSpectrum.basicOpen r))
  rw [congrArg (fun f => f.left) h]
  change IsOpenImmersion
    ((SmoothSiteAffineCoordinates.lineBaseOpen_isPullback
      (k := k) (PrimeSpectrum.basicOpen r)).isoPullback.inv ≫
      (polynomialProjection (.of R) ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι ≫
      (PolynomialOpenQuotient.ambientIso (algebraMap k R)).hom)
  infer_instance

omit [Algebra.Smooth k R] in
/-- The base-open Laurent model is cartesian with the original torus parameter. -/
theorem fixedPsiLaurentOpen_isPullback :
    IsPullback (laurentProjection (.of R) ∣_ PrimeSpectrum.basicOpen r)
      ((fixedPsiLaurentOpen R r).ι ≫
        Spec.map (CommRingCat.PolynomialLaurent.laurentMap
          (CommRingCat.ofHom (algebraMap k R))))
      (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫
        AffineTorusPolynomialPresentation.baseMap k R)
      (laurentProjection (.of k)) :=
  (isPullback_morphismRestrict (laurentProjection (.of R)) (PrimeSpectrum.basicOpen r)).paste_vert
    (AffineTorusPolynomialPresentation.ambient_isPullback k R)

/-- The original psi source is the literal torus cylinder of its original base open. -/
def neighborhoodPsiTorusIso :
    neighborhoodPsiSite k R (AffineTorusPolynomialPresentation.baseMap k R) r ≅
      SmoothSite.torusCylinder (.of k) (fixedPsiBaseSite R r k) :=
  MorphismProperty.Over.isoMk
    (fixedPsiLaurentOpenIso R r ≪≫ (fixedPsiLaurentOpen_isPullback R r k).isoPullback) (by
      change ((fixedPsiLaurentOpenIso R r).hom ≫
          (fixedPsiLaurentOpen_isPullback R r k).isoPullback.hom) ≫
          (pullback.fst
            (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫
              AffineTorusPolynomialPresentation.baseMap k R) (laurentProjection (.of k)) ≫
            (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫
              AffineTorusPolynomialPresentation.baseMap k R)) =
        fixedPsiProjection R r ≫ AffineTorusPolynomialPresentation.baseMap k R
      simp only [Category.assoc, IsPullback.isoPullback_hom_fst_assoc,
        morphismRestrict_ι_assoc]
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ AffineTorusPolynomialPresentation.baseMap k R)
        (fixedPsiLaurentOpenIso_projection R r))

/-- The comparison preserves the original projection to the unshrunk base. -/
@[reassoc] theorem neighborhoodPsiTorusIso_projection :
    (neighborhoodPsiTorusIso R r k).hom.left ≫
      (SmoothSite.productFst (fixedPsiBaseSite R r k) (SmoothSite.torus (.of k))).left ≫
        Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) =
          fixedPsiProjection R r := by
  change ((fixedPsiLaurentOpenIso R r).hom ≫
    (fixedPsiLaurentOpen_isPullback R r k).isoPullback.hom) ≫ (pullback.fst _ _ ≫ _) = _
  rw [Category.assoc, IsPullback.isoPullback_hom_fst_assoc, morphismRestrict_ι]
  exact fixedPsiLaurentOpenIso_projection R r

/-- The original torus coordinate is retained, before its affine open inclusion. -/
@[reassoc] theorem neighborhoodPsiTorusIso_parameter :
    (neighborhoodPsiTorusIso R r k).hom.left ≫
      (SmoothSite.productSnd (fixedPsiBaseSite R r k) (SmoothSite.torus (.of k))).left =
      (fixedPsiLaurentOpenIso R r).hom ≫ (fixedPsiLaurentOpen R r).ι ≫
        Spec.map (CommRingCat.PolynomialLaurent.laurentMap
          (CommRingCat.ofHom (algebraMap k R))) := by
  change ((fixedPsiLaurentOpenIso R r).hom ≫
    (fixedPsiLaurentOpen_isPullback R r k).isoPullback.hom) ≫ pullback.snd _ _ = _
  rw [Category.assoc, IsPullback.isoPullback_hom_snd]

/-- Through the literal contraction open and original polynomial product chart,
the comparison is exactly the original affine open inclusion. -/
@[reassoc] theorem neighborhoodPsiTorusIso_affine :
    (neighborhoodPsiTorusIso R r k).hom.left ≫
      (SmoothSite.contractionOpen (.of k) (fixedPsiBaseSite R r k)).left ≫
      (SmoothSite.a1Map (.of k) (SmoothSite.openInclusion
        (AffineTorusPolynomialPresentation.affineSite k R) (PrimeSpectrum.basicOpen r))).left =
      (fixedPsiSource R r).ι ≫ (PolynomialOpenQuotient.ambientIso (algebraMap k R)).hom := by
  change (show (fixedPsiSource R r).toScheme ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))
        (polynomialProjection (.of k)) from
      (neighborhoodPsiTorusIso R r k).hom.left ≫
        (SmoothSite.contractionOpen (.of k) (fixedPsiBaseSite R r k)).left ≫
        (SmoothSite.a1Map (.of k) (SmoothSite.openInclusion
          (AffineTorusPolynomialPresentation.affineSite k R) (PrimeSpectrum.basicOpen r))).left) =
    (fixedPsiSource R r).ι ≫ (PolynomialOpenQuotient.ambientIso (algebraMap k R)).hom
  apply pullback.hom_ext
  · have h₁ := congrArg (fun f => f.left)
      (SmoothSite.a1Map_projection (.of k) (SmoothSite.openInclusion
        (AffineTorusPolynomialPresentation.affineSite k R) (PrimeSpectrum.basicOpen r)))
    have h₂ := congrArg (fun f => f.left)
      (SmoothSite.productMap_fst (𝟙 (fixedPsiBaseSite R r k))
        (SmoothSite.torusInAffineLine (.of k)))
    change (SmoothSite.a1Map (.of k) (SmoothSite.openInclusion
        (AffineTorusPolynomialPresentation.affineSite k R) (PrimeSpectrum.basicOpen r))).left ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R)))
          (polynomialProjection (.of k)) =
      pullback.fst (fixedPsiBaseSite R r k).hom (polynomialProjection (.of k)) ≫
        Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) at h₁
    change (SmoothSite.contractionOpen (.of k) (fixedPsiBaseSite R r k)).left ≫
        pullback.fst (fixedPsiBaseSite R r k).hom (polynomialProjection (.of k)) =
      pullback.fst (fixedPsiBaseSite R r k).hom (laurentProjection (.of k)) ≫
        𝟙 ((fixedPsiBaseSite R r k).left) at h₂
    simp only [Category.assoc, PolynomialOpenQuotient.ambientIso_fst, h₁, reassoc_of% h₂]
    have hp := neighborhoodPsiTorusIso_projection R r k
    change (neighborhoodPsiTorusIso R r k).hom.left ≫
      pullback.fst (fixedPsiBaseSite R r k).hom (laurentProjection (.of k)) ≫
        Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) =
      (fixedPsiSource R r).ι ≫ polynomialProjection (.of R) at hp
    exact hp
  · have h₁ := congrArg (fun f => f.left)
      (SmoothSite.productMap_snd (SmoothSite.openInclusion
        (AffineTorusPolynomialPresentation.affineSite k R) (PrimeSpectrum.basicOpen r))
        (𝟙 (SmoothSite.affineLine (.of k))))
    have h₂ := congrArg (fun f => f.left)
      (SmoothSite.productMap_snd (𝟙 (fixedPsiBaseSite R r k))
        (SmoothSite.torusInAffineLine (.of k)))
    change (SmoothSite.a1Map (.of k) (SmoothSite.openInclusion
        (AffineTorusPolynomialPresentation.affineSite k R) (PrimeSpectrum.basicOpen r))).left ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k R)))
          (polynomialProjection (.of k)) =
      pullback.snd (fixedPsiBaseSite R r k).hom (polynomialProjection (.of k)) ≫
        𝟙 (Spec (.of (Polynomial k))) at h₁
    change (SmoothSite.contractionOpen (.of k) (fixedPsiBaseSite R r k)).left ≫
        pullback.snd (fixedPsiBaseSite R r k).hom (polynomialProjection (.of k)) =
      pullback.snd (fixedPsiBaseSite R r k).hom (laurentProjection (.of k)) ≫
        (SmoothSite.torusInAffineLine (.of k)).left at h₂
    simp only [Category.comp_id] at h₁
    simp only [Category.assoc, PolynomialOpenQuotient.ambientIso_snd, h₁, h₂]
    have hp := neighborhoodPsiTorusIso_parameter R r k
    change (neighborhoodPsiTorusIso R r k).hom.left ≫
      pullback.snd (fixedPsiBaseSite R r k).hom (laurentProjection (.of k)) =
        (fixedPsiLaurentOpenIso R r).hom ≫ (fixedPsiLaurentOpen R r).ι ≫
          Spec.map (CommRingCat.PolynomialLaurent.laurentMap
            (CommRingCat.ofHom (algebraMap k R))) at hp
    rw [reassoc_of% hp]
    have hn : Spec.map (CommRingCat.PolynomialLaurent.laurentMap
          (CommRingCat.ofHom (algebraMap k R))) ≫ laurentPlus (.of k) =
        laurentPlus (.of R) ≫ Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (algebraMap k R))) := by
      rw [laurentPlus, laurentPlus, ← Spec.map_comp, ← Spec.map_comp]
      exact congrArg Spec.map
        (CommRingCat.PolynomialLaurent.toLaurent_naturality
          (CommRingCat.ofHom (algebraMap k R))).symm
    change (fixedPsiLaurentOpenIso R r).hom ≫ (fixedPsiLaurentOpen R r).ι ≫
        Spec.map (CommRingCat.PolynomialLaurent.laurentMap
          (CommRingCat.ofHom (algebraMap k R))) ≫ laurentPlus (.of k) =
      (fixedPsiSource R r).ι ≫ Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (algebraMap k R)))
    rw [hn, fixedPsiLaurentOpenIso_ι_assoc]

end AlgebraicGeometry.RelativeProjectiveLine
