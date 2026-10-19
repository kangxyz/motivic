/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.LaurentChart
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Laurent
/-! # The original punctured relative line is the original smooth-site torus product -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open _root_.AlgebraicGeometry.Scheme
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
attribute [local instance] laurent_smooth

/-- Both original product projections are retained by the actual Laurent chart. -/
def laurentProductIso : sourceSite (k := k) (A := LaurentPolynomial R) ≅
    SmoothSite.product (sourceSite (k := k) (A := R)) (SmoothSite.torus (.of k)) :=
  MorphismProperty.Over.isoMk (_root_.AlgebraicGeometry.Scheme.PolynomialLaurent.ambientIso k R) (by
    change (_root_.AlgebraicGeometry.Scheme.PolynomialLaurent.ambientIso k R).hom ≫
      (pullback.fst _ _ ≫ _) = _
    rw [← Category.assoc, ambientIso_hom_fst]
    exact coefficient_base (k := k) (R := R) (A := LaurentPolynomial R))

/-- The original D(T) model and original torus product are canonically isomorphic. -/
def puncturedProductIso : openSite (k := k) (X : R[X]) ≅
    SmoothSite.product (sourceSite (k := k) (A := R)) (SmoothSite.torus (.of k)) :=
  (laurentSiteIso (k := k) (R := R)).symm ≪≫ laurentProductIso

@[reassoc (attr := simp)] theorem laurentProductIso_fst :
    (laurentProductIso (k := k) (R := R)).hom.left ≫
      pullback.fst (sourceSite (k := k) (A := R)).hom (laurentProjection (.of k)) =
        laurentProjection (.of R) :=
  ambientIso_hom_fst k R

@[reassoc (attr := simp)] theorem laurentProductIso_snd :
    (laurentProductIso (k := k) (R := R)).hom.left ≫
      pullback.snd (sourceSite (k := k) (A := R)).hom (laurentProjection (.of k)) =
        Spec.map (CommRingCat.PolynomialLaurent.laurentMap
          (CommRingCat.ofHom (algebraMap k R))) :=
  ambientIso_hom_snd

end AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
