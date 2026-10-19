/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeLaurentProductNaturality
/-! # The actual Laurent chart is natural for coefficient maps in the smooth site -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open _root_.AlgebraicGeometry.Scheme
variable {k R S : Type u} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra.Smooth k R] [Algebra k S] [Algebra.Smooth k S]
attribute [local instance] laurent_smooth

@[reassoc] theorem laurentMap_projection (φ : R →ₐ[k] S) :
    (laurentMap φ).left ≫ laurentProjection (.of R) =
      laurentProjection (.of S) ≫ (SmoothSite.affineMorphism φ).left := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact CommRingCat.PolynomialLaurent.laurentMap_C (CommRingCat.ofHom φ.toRingHom) r

@[reassoc] theorem laurentMap_field (φ : R →ₐ[k] S) :
    (laurentMap φ).left ≫ Spec.map (CommRingCat.PolynomialLaurent.laurentMap
      (CommRingCat.ofHom (algebraMap k R))) =
      Spec.map (CommRingCat.PolynomialLaurent.laurentMap
        (CommRingCat.ofHom (algebraMap k S))) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.PolynomialLaurent.laurentMap_comp]
  congr 2
  ext r
  exact φ.commutes r

/-- The original relative product, with both projections unchanged. -/
theorem laurentProductIso_naturality (φ : R →ₐ[k] S) :
    laurentMap φ ≫ (laurentProductIso (k := k) (R := R)).hom =
      (laurentProductIso (k := k) (R := S)).hom ≫
        SmoothSite.productMap (SmoothSite.affineMorphism φ)
          (𝟙 (SmoothSite.torus (.of k))) := by
  apply SmoothSite.product_hom_ext
  · rw [Category.assoc, Category.assoc, SmoothSite.productMap_fst, ← Category.assoc]
    apply MorphismProperty.Over.Hom.ext
    change ((laurentMap φ).left ≫ (laurentProductIso (k := k) (R := R)).hom.left) ≫
      pullback.fst (sourceSite (k := k) (A := R)).hom (laurentProjection (.of k)) =
      (laurentProductIso (k := k) (R := S)).hom.left ≫
        (pullback.fst (sourceSite (k := k) (A := S)).hom (laurentProjection (.of k)) ≫
          (SmoothSite.affineMorphism φ).left)
    rw [Category.assoc, laurentProductIso_fst, ← Category.assoc, laurentProductIso_fst]
    exact laurentMap_projection φ
  · rw [Category.assoc, Category.assoc, SmoothSite.productMap_snd, Category.comp_id]
    apply MorphismProperty.Over.Hom.ext
    change ((laurentMap φ).left ≫ (laurentProductIso (k := k) (R := R)).hom.left) ≫
      pullback.snd (sourceSite (k := k) (A := R)).hom (laurentProjection (.of k)) =
      (laurentProductIso (k := k) (R := S)).hom.left ≫
        pullback.snd (sourceSite (k := k) (A := S)).hom (laurentProjection (.of k))
    rw [Category.assoc, laurentProductIso_snd, laurentProductIso_snd]
    exact laurentMap_field φ

/-- The original punctured-line presentation is natural with respect to actual base change. -/
theorem puncturedProductIso_naturality (φ : R →ₐ[k] S) :
    puncturedBaseMap φ ≫ (puncturedProductIso (k := k) (R := R)).hom =
      (puncturedProductIso (k := k) (R := S)).hom ≫
        SmoothSite.productMap (SmoothSite.affineMorphism φ)
          (𝟙 (SmoothSite.torus (.of k))) := by
  apply (cancel_epi (laurentSiteIso (k := k) (R := S)).hom).mp
  rw [← Category.assoc, ← laurentSiteIso_naturality]
  simp only [puncturedProductIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact laurentProductIso_naturality φ

end AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
