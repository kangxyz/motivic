/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.Coordinates
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeAffineLineOpenMaps
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.PolynomialQuotientCoordinates
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Projection
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Field
/-! # Actual polynomial coordinates for original affine cylinders -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.SmoothSite
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- The literal polynomial spectrum is the original relative product. -/
def lineCylinderIso : lineSite (k := k) (R := R) ≅
    a1Cylinder (.of k) (affineSite k R) :=
  MorphismProperty.Over.isoMk (ambientIso (algebraMap k R)) (by
    change (ambientIso (algebraMap k R)).hom ≫
      (pullback.fst _ _ ≫ _) = _
    rw [← Category.assoc, ambientIso_fst]
    rfl)

@[reassoc (attr := simp)] theorem lineCylinderIso_projection :
    (lineCylinderIso (k := k) (R := R)).hom ≫
      a1Projection (.of k) (affineSite k R) =
      homMk (polynomialProjection (.of R)) rfl := by
  apply MorphismProperty.Over.Hom.ext
  exact ambientIso_fst (algebraMap k R)

/-- The actual cylinder operation carries a site isomorphism to an isomorphism. -/
def cylinderIso {X Y : SmoothSite (Spec (.of k))} (e : X ≅ Y) :
    a1Cylinder (.of k) X ≅ a1Cylinder (.of k) Y where
  hom := a1Map (.of k) e.hom
  inv := a1Map (.of k) e.inv
  hom_inv_id := by rw [← a1Map_comp, e.hom_inv_id, a1Map_id]
  inv_hom_id := by rw [← a1Map_comp, e.inv_hom_id, a1Map_id]

attribute [local instance] sectionsAlgebra

/-- No replacement of the original affine source or its cylinder is made. -/
def affineLineIso (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    lineSite (k := k) (R := Γ(X.left, ⊤)) ≅ a1Cylinder (.of k) X :=
  lineCylinderIso ≪≫ cylinderIso (affineIso X)

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.PolynomialOpenQuotient
open scoped Polynomial
namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
attribute [local instance]
    _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.sectionsAlgebra
/-- The canonical affine-cylinder comparison retains the literal scalar parameter. -/
theorem affineLineIso_parameter :
    (affineLineIso X).hom.left ≫ pullback.snd X.hom
        (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (scalarMap X))) := by
  have hm := congrArg (fun f => f.left)
    (SmoothSite.productMap_snd (affineIso X).hom
      (𝟙 (SmoothSite.affineLine (.of k))))
  change (SmoothSite.a1Map (.of k) (affineIso X).hom).left ≫
      pullback.snd X.hom (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom =
      pullback.snd (Spec.map (CommRingCat.ofHom (scalarMap X)))
        (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom ≫ 𝟙 _ at hm
  rw [Category.comp_id] at hm
  change (ambientIso (scalarMap X)).hom ≫
      (SmoothSite.a1Map (.of k) (affineIso X).hom).left ≫
      pullback.snd X.hom (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom = _
  erw [hm, ambientIso_snd]


end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
end
