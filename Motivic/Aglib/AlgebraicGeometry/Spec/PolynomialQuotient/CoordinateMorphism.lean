/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.SmoothSite

/-!
# Coordinate morphisms for polynomial quotients
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open _root_.AlgebraicGeometry.Scheme
variable {k R A : Type u} [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra.Smooth k R] [Algebra R A] [Algebra k A]
    [IsScalarTower k R A] [Algebra.Smooth k A]

/-- The original affine-line coordinate map, with its actual structural equation. -/
def coordinateMorphism (a : A) :
    sourceSite (k := k) (A := A) ⟶ lineSite (k := k) (R := R) :=
  SmoothSite.homMk (Spec.map (CommRingCat.ofHom (eval₂RingHom (algebraMap R A) a))) (by
    change Spec.map _ ≫ (Spec.map _ ≫ Spec.map _) = _
    rw [← coefficient_base (k := k) (R := R) (A := A), ← Category.assoc]
    congr 1
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact eval₂_C _ _)

end AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
