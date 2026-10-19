/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Torus
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products

/-!
# The actual affine-line projection on the smooth site

The affine line is the spectrum of the polynomial ring. Its cylinder uses the
literal relative scheme product, and each constant section is induced by actual
polynomial evaluation. The projection and section identities here will determine
the maps in homotopy invariance; no invariance theorem is asserted.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (R : CommRingCat.{u})

/-- The affine line is the literal polynomial spectrum over its coefficient ring. -/
def affineLine : SmoothSite (Spec R) :=
  mk (polynomialProjection R)

@[simp] theorem affineLine_left :
    (affineLine R).left = Spec (.of (Polynomial R)) := rfl

@[simp] theorem affineLine_hom :
    (affineLine R).hom = polynomialProjection R := rfl

/-- Evaluation at a coefficient gives the actual constant point of the affine line. -/
def affineLinePoint (a : R) : base (Spec R) ⟶ affineLine R :=
  homMk (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) (by
    have h : CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom a) = 𝟙 R := by
      ext r
      exact Polynomial.eval_C
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, h, Spec.map_id]
    rfl)

@[simp] theorem affineLinePoint_left (a : R) :
    (affineLinePoint R a).left =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) := rfl

/-- The actual scheme cylinder, with the affine line as the second factor. -/
def a1Cylinder (X : SmoothSite (Spec R)) : SmoothSite (Spec R) :=
  product X (affineLine R)

/-- The actual projection `X × A¹ → X`. -/
def a1Projection (X : SmoothSite (Spec R)) : a1Cylinder R X ⟶ X :=
  productFst X (affineLine R)

@[simp] theorem a1Projection_left (X : SmoothSite (Spec R)) :
    (a1Projection R X).left =
      CategoryTheory.Limits.pullback.fst X.hom (polynomialProjection R) := rfl

/-- The cylinder map is the actual product of a map with the affine-line identity. -/
def a1Map {X Y : SmoothSite (Spec R)} (f : X ⟶ Y) :
    a1Cylinder R X ⟶ a1Cylinder R Y :=
  productMap f (𝟙 (affineLine R))

@[reassoc (attr := simp)]
theorem a1Map_projection {X Y : SmoothSite (Spec R)} (f : X ⟶ Y) :
    a1Map R f ≫ a1Projection R Y = a1Projection R X ≫ f :=
  productMap_fst f (𝟙 _)

@[simp] theorem a1Map_id (X : SmoothSite (Spec R)) :
    a1Map R (𝟙 X) = 𝟙 (a1Cylinder R X) := productMap_id _ _

@[simp] theorem a1Map_comp {X Y Z : SmoothSite (Spec R)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    a1Map R (f ≫ g) = a1Map R f ≫ a1Map R g := by
  simpa only [a1Map, Category.id_comp] using productMap_comp f g
    (𝟙 (affineLine R)) (𝟙 (affineLine R))

/-- The actual constant section of the cylinder. -/
def a1Section (X : SmoothSite (Spec R)) (a : R) : X ⟶ a1Cylinder R X :=
  productLift (𝟙 X)
    ((homMk X.hom (Category.comp_id _) : X ⟶ base (Spec R)) ≫ affineLinePoint R a)

@[reassoc (attr := simp)]
theorem a1Section_projection (X : SmoothSite (Spec R)) (a : R) :
    a1Section R X a ≫ a1Projection R X = 𝟙 X :=
  productLift_fst _ _

@[reassoc (attr := simp)]
theorem a1Section_naturality {X Y : SmoothSite (Spec R)} (f : X ⟶ Y) (a : R) :
    a1Section R X a ≫ a1Map R f = f ≫ a1Section R Y a := by
  apply product_hom_ext
  · simp [a1Map, a1Section]
  · simp only [a1Map, a1Section, Category.assoc, productMap_snd,
      productLift_snd, Category.comp_id]
    rw [← Category.assoc]
    congr 1
    apply MorphismProperty.Over.Hom.ext
    exact (MorphismProperty.Over.w f).symm

end AlgebraicGeometry.Scheme.SmoothSite
