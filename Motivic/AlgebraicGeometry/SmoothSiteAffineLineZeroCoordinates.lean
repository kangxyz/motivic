/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteAffineLineCoordinates
public import Motivic.Aglib.AlgebraicGeometry.AffineLineZeroNeighborhoodBaseShrink

/-! # Canonical affine coordinates preserve the entire original zero morphism

These are equalities of scheme morphisms, rather than identifications of zero
supports. They transport the original whole-zero étale square to polynomial
coordinates without a rationality assumption on any selected point.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.PolynomialOpenQuotient

universe u

namespace Motivic.SmoothSiteAffineCoordinates

open AffineTorusPolynomialPresentation

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- Polynomial evaluation at zero is the literal zero section of the product chart. -/
@[reassoc] theorem lineCylinderIso_zero :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
      (lineCylinderIso (k := k) (R := R)).hom.left =
        (SmoothSite.a1Section (.of k) (affineSite k R) 0).left := by
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
    (ambientIso (algebraMap k R)).hom =
      (show Spec (.of R) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))
        (Scheme.PolynomialLaurent.polynomialProjection (.of k)) from
          (SmoothSite.a1Section (.of k) (affineSite k R) 0).left)
  apply pullback.hom_ext
  · rw [Category.assoc, ambientIso_fst]
    change Spec.map _ ≫ Spec.map _ = pullback.lift _ _ _ ≫ pullback.fst _ _
    rw [pullback.lift_fst, ← Spec.map_comp]
    have he : CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)) = 𝟙 (CommRingCat.of R) := by
      ext x
      simp
    rw [he, Spec.map_id]
    rfl
  · rw [Category.assoc, ambientIso_snd]
    change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k R))) =
      pullback.lift _ _ _ ≫ pullback.snd _ _
    rw [pullback.lift_snd]
    exact Scheme.polynomial_zero_scalar_naturality (algebraMap k R)

attribute [local instance] sectionsAlgebra

/-- The canonical affine-cylinder coordinates retain the whole original zero section. -/
@[reassoc] theorem affineLineIso_zero
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : Γ(X.left, ⊤)))) ≫
      (affineLineIso X).hom.left =
        (affineIso X).hom.left ≫ (SmoothSite.a1Section (.of k) X 0).left := by
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : Γ(X.left, ⊤)))) ≫
      (lineCylinderIso (k := k) (R := Γ(X.left, ⊤))).hom.left ≫
        (SmoothSite.a1Map (.of k) (affineIso X).hom).left = _
  rw [← Category.assoc, lineCylinderIso_zero]
  exact congrArg (fun f => f.left)
    (SmoothSite.a1Section_naturality (.of k) (affineIso X).hom 0)

/-- The original full zero-fiber square remains cartesian in canonical polynomial
coordinates, before choosing a point or a presentation. -/
theorem affineLineIso_wholeZero_isPullback
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
    {Y : Scheme.{u}} (p : Y ⟶ (SmoothSite.a1Cylinder (.of k) X).left)
    (a : X.left ⟶ Y)
    (H : IsPullback a (𝟙 X.left) p (SmoothSite.a1Section (.of k) X 0).left) :
    IsPullback ((affineIso X).hom.left ≫ a) (𝟙 _)
      (p ≫ (affineLineIso X).inv.left)
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : Γ(X.left, ⊤))))) := by
  let e := (SmoothSite.forgetScheme (Spec (.of k))).mapIso (affineIso X)
  let eL := (SmoothSite.forgetScheme (Spec (.of k))).mapIso (affineLineIso X)
  apply H.of_iso' e (Iso.refl _) e eL
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · exact (Category.comp_id e.hom).trans (Category.id_comp e.hom).symm
  · change p = (p ≫ eL.inv) ≫ eL.hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · exact (affineLineIso_zero X).symm

end Motivic.SmoothSiteAffineCoordinates
