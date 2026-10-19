/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.CoordinateMorphism
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Torus

/-! # Extracted ordinary primitive with the original parameters and maps -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe v u
namespace AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
/-- Smoothness of the original Laurent algebra, obtained from its actual open immersion. -/
theorem laurent_smooth : Algebra.Smooth k (LaurentPolynomial R) := by
  have h : Smooth (laurentProjection (.of R)) := inferInstance
  rw [laurentProjection, HasRingHomProperty.Spec_iff (P := @Smooth)] at h
  let : Algebra.Smooth R (LaurentPolynomial R) := RingHom.smooth_algebraMap.mp h
  exact Algebra.Smooth.comp k R (LaurentPolynomial R)

attribute [local instance] laurent_smooth

/-- The unchanged Laurent spectrum is the unchanged relative principal open D(T). -/
def laurentSchemeIso : Spec (.of (LaurentPolynomial R)) ≅ (principalOpen (X : R[X])).toScheme :=
  IsOpenImmersion.isoOfRangeEq (laurentPlus (.of R)) (principalOpen (X : R[X])).ι (by
    rw [Scheme.Opens.range_ι]
    exact congrArg (fun U : (Spec (.of R[X])).Opens => (U : Set (Spec (.of R[X]))))
      (laurentPlus_opensRange (.of R)))

/-- This is an isomorphism in the original smooth site over k, not over a new field. -/
def laurentSiteIso : sourceSite (k := k) (A := LaurentPolynomial R) ≅
    openSite (k := k) (X : R[X]) :=
  MorphismProperty.Over.isoMk (laurentSchemeIso (R := R)) (by
    change (laurentSchemeIso (R := R)).hom ≫ ((principalOpen (X : R[X])).ι ≫
      (polynomialProjection (.of R) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))) = _
    rw [← Category.assoc, laurentSchemeIso, IsOpenImmersion.isoOfRangeEq_hom_fac,
      ← Category.assoc, laurentPlus_projection]
    exact coefficient_base (k := k) (R := R) (A := LaurentPolynomial R))

/-- The coordinate of the original torus is exactly T, with its actual coefficient map. -/
theorem laurentSiteIso_coordinate :
    (laurentSiteIso (k := k) (R := R)).hom ≫ openInclusion (k := k) (X : R[X]) =
      coordinateMorphism (k := k) (R := R) (LaurentPolynomial.T 1) := by
  apply MorphismProperty.Over.Hom.ext
  change (laurentSchemeIso (R := R)).hom ≫ (principalOpen (X : R[X])).ι = _
  rw [laurentSchemeIso, IsOpenImmersion.isoOfRangeEq_hom_fac]
  change Spec.map (CommRingCat.ofHom
    (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R)) = Spec.map _
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change Polynomial.toLaurent (C r) = Polynomial.eval₂ _ _ (C r)
    rw [eval₂_C]
    exact Polynomial.toLaurent_C r
  · change Polynomial.toLaurent X = Polynomial.eval₂ _ _ X
    rw [eval₂_X]
    exact Polynomial.toLaurent_X

end AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
