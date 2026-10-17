/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.RelativeLaurentProductCoordinates
public import Motivic.AlgebraicGeometry.Correspondences.RelativeAffineLineOpenMaps
/-! # Original product and punctured-line coefficient maps agree naturally -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace Motivic.RelativePolynomialOpenSpans
variable {k R S : Type u} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra.Smooth k R] [Algebra k S] [Algebra.Smooth k S]
attribute [local instance] laurent_smooth

/-- The actual coefficient map between original Laurent spectra. -/
def laurentMap (φ : R →ₐ[k] S) : sourceSite (k := k) (A := LaurentPolynomial S) ⟶
    sourceSite (k := k) (A := LaurentPolynomial R) :=
  SmoothSite.homMk (Spec.map (CommRingCat.PolynomialLaurent.laurentMap
    (CommRingCat.ofHom φ.toRingHom))) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      change (CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom φ.toRingHom))
        (LaurentPolynomial.C (algebraMap k R r)) = LaurentPolynomial.C (algebraMap k S r)
      rw [CommRingCat.PolynomialLaurent.laurentMap_C]
      exact congrArg LaurentPolynomial.C (φ.commutes r))

@[reassoc] theorem laurentMap_plus (φ : R →ₐ[k] S) :
    (laurentMap φ).left ≫ laurentPlus (.of R) =
      laurentPlus (.of S) ≫ (lineMap φ).left := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.PolynomialLaurent.toLaurent_naturality
    (CommRingCat.ofHom φ.toRingHom)).symm

/-- The punctured-line isomorphism preserves the original coefficient maps. -/
theorem laurentSiteIso_naturality (φ : R →ₐ[k] S) :
    laurentMap φ ≫ (laurentSiteIso (k := k) (R := R)).hom =
      (laurentSiteIso (k := k) (R := S)).hom ≫ puncturedBaseMap φ := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono (principalOpen (X : R[X])).ι).mp
  change ((_ ≫ _) ≫ _) = ((_ ≫ _) ≫ _)
  have hr : (laurentSiteIso (k := k) (R := R)).hom.left ≫
      (principalOpen (X : R[X])).ι = laurentPlus (.of R) := by
    change (laurentSchemeIso (R := R)).hom ≫ _ = _
    unfold laurentSchemeIso
    exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hs : (laurentSiteIso (k := k) (R := S)).hom.left ≫
      (principalOpen (X : S[X])).ι = laurentPlus (.of S) := by
    change (laurentSchemeIso (R := S)).hom ≫ _ = _
    unfold laurentSchemeIso
    exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hb := openMapOfLE_inclusion φ (principalOpen X) (principalOpen X) (punctured_preimage φ)
  erw [Category.assoc, hr, Category.assoc, hb, ← Category.assoc, hs]
  exact laurentMap_plus φ

end Motivic.RelativePolynomialOpenSpans
