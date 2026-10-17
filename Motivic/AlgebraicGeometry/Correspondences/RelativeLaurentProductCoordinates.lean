/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.RelativeLaurentRestrictionInjective
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.Contraction
/-! # The original punctured relative line is the original smooth-site torus product -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace Motivic.RelativePolynomialOpenSpans
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
attribute [local instance] laurent_smooth

/-- Both original product projections are retained by the actual Laurent chart. -/
def laurentProductIso : sourceSite (k := k) (A := LaurentPolynomial R) ≅
    SmoothSite.product (sourceSite (k := k) (A := R)) (SmoothSite.torus (.of k)) :=
  MorphismProperty.Over.isoMk (AffineTorusPolynomialPresentation.ambientIso k R) (by
    change (AffineTorusPolynomialPresentation.ambientIso k R).hom ≫
      (pullback.fst _ _ ≫ _) = _
    rw [← Category.assoc, AffineTorusPolynomialPresentation.ambientIso_hom_fst]
    exact coefficient_base (k := k) (R := R) (A := LaurentPolynomial R))

/-- The original D(T) model and original torus product are canonically isomorphic. -/
def puncturedProductIso : openSite (k := k) (X : R[X]) ≅
    SmoothSite.product (sourceSite (k := k) (A := R)) (SmoothSite.torus (.of k)) :=
  (laurentSiteIso (k := k) (R := R)).symm ≪≫ laurentProductIso

@[reassoc (attr := simp)] theorem laurentProductIso_fst :
    (laurentProductIso (k := k) (R := R)).hom.left ≫ pullback.fst _ _ =
      laurentProjection (.of R) :=
  AffineTorusPolynomialPresentation.ambientIso_hom_fst k R

@[reassoc (attr := simp)] theorem laurentProductIso_snd :
    (laurentProductIso (k := k) (R := R)).hom.left ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.PolynomialLaurent.laurentMap
        (CommRingCat.ofHom (algebraMap k R))) :=
  AffineTorusPolynomialPresentation.ambientIso_hom_snd

end Motivic.RelativePolynomialOpenSpans
