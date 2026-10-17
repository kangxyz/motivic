/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.SmoothSiteAffineCoordinates
public import Motivic.AlgebraicGeometry.Correspondences.RelativeAffineLineOpenMaps
public import Motivic.Aglib.AlgebraicGeometry.PolynomialQuotientCoordinates
public import Motivic.Cohomology.A1.Projection
/-! # Actual polynomial coordinates for original affine cylinders -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace Motivic.SmoothSiteAffineCoordinates
open RelativePolynomialOpenSpans AffineTorusPolynomialPresentation
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- The literal polynomial spectrum is the original relative product. -/
def lineCylinderIso : lineSite (k := k) (R := R) ≅
    SmoothSite.a1Cylinder (.of k) (affineSite k R) :=
  MorphismProperty.Over.isoMk (ambientIso (algebraMap k R)) (by
    change (ambientIso (algebraMap k R)).hom ≫
      (pullback.fst _ _ ≫ _) = _
    rw [← Category.assoc, ambientIso_fst]
    rfl)

@[reassoc (attr := simp)] theorem lineCylinderIso_projection :
    (lineCylinderIso (k := k) (R := R)).hom ≫
      SmoothSite.a1Projection (.of k) (affineSite k R) =
      SmoothSite.homMk (polynomialProjection (.of R)) rfl := by
  apply MorphismProperty.Over.Hom.ext
  exact ambientIso_fst (algebraMap k R)

/-- The actual cylinder operation carries a site isomorphism to an isomorphism. -/
def cylinderIso {X Y : SmoothSite (Spec (.of k))} (e : X ≅ Y) :
    SmoothSite.a1Cylinder (.of k) X ≅ SmoothSite.a1Cylinder (.of k) Y where
  hom := SmoothSite.a1Map (.of k) e.hom
  inv := SmoothSite.a1Map (.of k) e.inv
  hom_inv_id := by rw [← SmoothSite.a1Map_comp, e.hom_inv_id, SmoothSite.a1Map_id]
  inv_hom_id := by rw [← SmoothSite.a1Map_comp, e.inv_hom_id, SmoothSite.a1Map_id]

attribute [local instance] sectionsAlgebra

/-- No replacement of the original affine source or its cylinder is made. -/
def affineLineIso (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    lineSite (k := k) (R := Γ(X.left, ⊤)) ≅ SmoothSite.a1Cylinder (.of k) X :=
  lineCylinderIso ≪≫ cylinderIso (affineIso X)

end Motivic.SmoothSiteAffineCoordinates
