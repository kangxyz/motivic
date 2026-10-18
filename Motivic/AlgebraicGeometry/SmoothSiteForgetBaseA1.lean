/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteForgetBase
public import Motivic.Cohomology.A1.Projection
public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # The original cylinder projection after forgetting a finite separable base -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace Motivic.SmoothSite

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

local notation "r" => finiteSeparableBaseMap k L
local notation "F" => finiteSeparableForgetBase k L
local notation "φ" => CommRingCat.ofHom (algebraMap k L)

omit [Module.Finite k L] [Algebra.IsSeparable k L] in
/-- The literal polynomial coefficient square is Cartesian. -/
theorem finiteSeparablePolynomial_isPullback :
    IsPullback (polynomialProjection (.of L))
      (Spec.map (CommRingCat.PolynomialLaurent.polynomialMap φ))
      r (polynomialProjection (.of k)) := by
  have h := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.PolynomialLaurent.polynomial_isPushout φ)
  simpa only [CommRingCat.PolynomialLaurent.coefficient, polynomialProjection] using h

omit [Module.Finite k L] [Algebra.IsSeparable k L] in
/-- The forgotten original cylinder is a pullback over the original k-base. -/
theorem finiteSeparableCylinder_isPullback (X : SmoothSite (Spec (.of L))) :
    IsPullback (a1Projection (.of L) X).left
      (pullback.snd X.hom (polynomialProjection (.of L)) ≫
        Spec.map (CommRingCat.PolynomialLaurent.polynomialMap φ))
      (X.hom ≫ r) (polynomialProjection (.of k)) :=
  (IsPullback.of_hasPullback X.hom (polynomialProjection (.of L))).paste_vert
    (finiteSeparablePolynomial_isPullback k L)

/-- The comparison keeps the actual schemes and the original projection map. -/
def finiteSeparableForgetBaseA1Iso (X : SmoothSite (Spec (.of L))) :
    (F).obj (a1Cylinder (.of L) X) ≅ a1Cylinder (.of k) ((F).obj X) :=
  MorphismProperty.Over.isoMk (finiteSeparableCylinder_isPullback k L X).isoPullback (by
    change (finiteSeparableCylinder_isPullback k L X).isoPullback.hom ≫
      (pullback.fst (X.hom ≫ r) (polynomialProjection (.of k)) ≫ (X.hom ≫ r)) =
        (pullback.fst X.hom (polynomialProjection (.of L)) ≫ X.hom) ≫ r
    rw [← Category.assoc, IsPullback.isoPullback_hom_fst]
    simp only [a1Projection_left, Category.assoc])

/-- The original L-projection becomes the original k-projection through the actual comparison. -/
@[reassoc]
theorem finiteSeparableForgetBaseA1Iso_hom_projection (X : SmoothSite (Spec (.of L))) :
    (finiteSeparableForgetBaseA1Iso k L X).hom ≫ a1Projection (.of k) ((F).obj X) =
      (F).map (a1Projection (.of L) X) := by
  apply MorphismProperty.Over.Hom.ext
  exact (finiteSeparableCylinder_isPullback k L X).isoPullback_hom_fst

end Motivic.SmoothSite
