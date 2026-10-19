/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RelativeLaurentProductCoordinates
public import Motivic.AlgebraicGeometry.SmoothSiteAffineLineCoordinates
public import Aglib.Algebra.Polynomial.Laurent.BaseChange

/-! # The original punctured polynomial chart retains its ambient inclusion -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace Motivic.RelativePolynomialOpenSpans
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
attribute [local instance] laurent_smooth

/-- Both charts identify the same literal D(X) inclusion, including its coefficient
and Laurent coordinate; no new open or ambient map is substituted. -/
@[reassoc]
theorem puncturedProductIso_open :
    (puncturedProductIso (k := k) (R := R)).hom ≫
      SmoothSite.contractionOpen (.of k) (AffineTorusPolynomialPresentation.affineSite k R) =
    openInclusion (k := k) (X : R[X]) ≫
      (SmoothSiteAffineCoordinates.lineCylinderIso (k := k) (R := R)).hom := by
  apply (cancel_epi (laurentSiteIso (k := k) (R := R)).hom).mp
  simp only [puncturedProductIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  apply MorphismProperty.Over.Hom.ext
  change (AffineTorusPolynomialPresentation.ambientIso k R).hom ≫
      (SmoothSite.contractionOpen (.of k)
        (AffineTorusPolynomialPresentation.affineSite k R)).left =
    (laurentSchemeIso (R := R)).hom ≫ ((principalOpen (X : R[X])).ι ≫
      (AlgebraicGeometry.PolynomialOpenQuotient.ambientIso (algebraMap k R)).hom)
  rw [← Category.assoc, laurentSchemeIso, IsOpenImmersion.isoOfRangeEq_hom_fac]
  have hf : (SmoothSite.contractionOpen (.of k)
        (AffineTorusPolynomialPresentation.affineSite k R)).left ≫
      pullback.fst _ _ = pullback.fst _ _ := by
    have h := congrArg (fun f => f.left) (SmoothSite.productMap_fst
      (𝟙 (AffineTorusPolynomialPresentation.affineSite k R))
      (SmoothSite.torusInAffineLine (.of k)))
    change (SmoothSite.contractionOpen (.of k)
        (AffineTorusPolynomialPresentation.affineSite k R)).left ≫
      pullback.fst _ _ = pullback.fst _ _ ≫ 𝟙 (Spec (.of R)) at h
    simpa only [Category.comp_id] using h
  have hs : (SmoothSite.contractionOpen (.of k)
        (AffineTorusPolynomialPresentation.affineSite k R)).left ≫
      pullback.snd _ _ = pullback.snd _ _ ≫ laurentPlus (.of k) := by
    have h := congrArg (fun f => f.left) (SmoothSite.productMap_snd
      (𝟙 (AffineTorusPolynomialPresentation.affineSite k R))
      (SmoothSite.torusInAffineLine (.of k)))
    change (SmoothSite.contractionOpen (.of k)
        (AffineTorusPolynomialPresentation.affineSite k R)).left ≫
      pullback.snd _ _ = pullback.snd _ _ ≫ laurentPlus (.of k) at h
    exact h
  apply pullback.hom_ext
  · rw [Category.assoc, hf, AffineTorusPolynomialPresentation.ambientIso_hom_fst,
      Category.assoc, AlgebraicGeometry.PolynomialOpenQuotient.ambientIso_fst,
      laurentPlus_projection]
  · rw [Category.assoc, hs, ← Category.assoc,
      AffineTorusPolynomialPresentation.ambientIso_hom_snd,
      Category.assoc, AlgebraicGeometry.PolynomialOpenQuotient.ambientIso_snd]
    rw [laurentPlus, laurentPlus, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.PolynomialLaurent.toLaurent_naturality
      (CommRingCat.ofHom (algebraMap k R))).symm

end Motivic.RelativePolynomialOpenSpans
