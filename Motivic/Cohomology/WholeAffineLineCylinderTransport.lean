/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteAffineLineOpenMaps

/-! # Actual relative-line restrictions under original cylinder coordinates

The arbitrary-presheaf comparison is separated from ordinary cohomology. Both
coefficient maps and the whole final base-open cylinder are explicit.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u w
namespace Motivic.SmoothSiteAffineCoordinates
open RelativePolynomialOpenSpans AffineTorusPolynomialPresentation
variable {k R S T : Type u} [Field k] [CommRing R] [CommRing S] [CommRing T]
  [Algebra k R] [Algebra.Smooth k R] [Algebra k S] [Algebra.Smooth k S]
  [Algebra k T] [Algebra.Smooth k T]

/-- The original two coefficient restrictions and final base-open restriction
commute with the actual whole-cylinder comparison. -/
theorem lineBaseOpenCylinder_two_maps {X : SmoothSite (Spec (.of k))}
    (e : affineSite k R ≅ X) (φ : R →ₐ[k] S) (ψ : S →ₐ[k] T)
    (V : (Spec (.of T)).Opens) :
    (lineBaseOpenCylinderIso (k := k) V).hom ≫
        SmoothSite.a1Map (.of k) (SmoothSite.openInclusion (affineSite k T) V ≫
          affineMorphism ψ ≫ affineMorphism φ ≫ e.hom) =
      (SmoothSite.openInclusion (lineSite (k := k) (R := T))
        (polynomialProjection (.of T) ⁻¹ᵁ V) ≫ lineMap ψ ≫ lineMap φ) ≫
          (lineCylinderIso (k := k) (R := R) ≪≫ cylinderIso e).hom := by
  simp only [SmoothSite.a1Map_comp, Iso.trans_hom, cylinderIso]
  rw [← Category.assoc, lineBaseOpenCylinderIso_comp]
  simp only [Category.assoc]
  rw [← lineCylinderIso_naturality_assoc ψ, ← lineCylinderIso_naturality_assoc φ]

/-- Zero is transported through an actual source isomorphism, without changing
coefficient objects or using any gluing property for the presheaf. -/
theorem cylinder_restriction_zero_of_lineBaseOpen {X : SmoothSite (Spec (.of k))}
    (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{w})
    (e : affineSite k R ≅ X) (φ : R →ₐ[k] S) (ψ : S →ₐ[k] T)
    (V : (Spec (.of T)).Opens)
    (x : P.obj (op (SmoothSite.a1Cylinder (.of k) X)))
    (hx : P.map (SmoothSite.openInclusion (lineSite (k := k) (R := T))
        (polynomialProjection (.of T) ⁻¹ᵁ V) ≫ lineMap ψ ≫ lineMap φ).op
      (P.map (lineCylinderIso (k := k) (R := R) ≪≫ cylinderIso e).hom.op x) = 0) :
    P.map (SmoothSite.a1Map (.of k)
      (SmoothSite.openInclusion (affineSite k T) V ≫
        affineMorphism ψ ≫ affineMorphism φ ≫ e.hom)).op x = 0 := by
  apply (ConcreteCategory.bijective_of_isIso
    (P.map (lineBaseOpenCylinderIso (k := k) V).hom.op)).injective
  rw [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    lineBaseOpenCylinder_two_maps, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  exact hx

end Motivic.SmoothSiteAffineCoordinates
