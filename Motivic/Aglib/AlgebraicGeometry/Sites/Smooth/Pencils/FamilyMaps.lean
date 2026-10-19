/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.Polynomial.FiniteFlat
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeEndpointSupportDiagram

/-!
# Family maps for smooth-site pencils
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.PolynomialPencil

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  {C : Scheme.{u}} (p : C ⟶ X.left)
  [Smooth (p ≫ X.hom)] [IsSeparated (p ≫ X.hom)] [QuasiCompact (p ≫ X.hom)]
  (L : LineBundle C) (a c : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
  (g : C ⟶ Y.left) (h : p ≫ X.hom = g ≫ Y.hom)

/-- The source map from the actual pencil zero scheme to the affine-line cylinder over `X`. -/
abbrev familySource := Hom.zeroInclusion (familyMap (p ≫ X.hom) L a c) ≫ parameterMap X.hom p
/-- The target map from the same pencil zero scheme through the original projection and `g`. -/
abbrev familyTarget := Hom.zeroInclusion (familyMap (p ≫ X.hom) L a c) ≫ projection (p ≫ X.hom) ≫ g

include h
omit [Smooth (p ≫ X.hom)] [IsSeparated (p ≫ X.hom)] [QuasiCompact (p ≫ X.hom)] in
/-- The literal family maps retain the original equation over the ground field. -/
theorem family_base : familySource p L a c ≫ relativeLineHom X.hom =
    familyTarget p L a c g ≫ Y.hom := by
  change (Hom.zeroInclusion _ ≫ parameterMap X.hom p) ≫
      (projection X.hom ≫ X.hom) = _
  rw [Category.assoc, ← Category.assoc (parameterMap X.hom p), parameterMap_projection]
  simp only [familyTarget, Category.assoc, h]


end AlgebraicGeometry.Scheme.SmoothSite.PolynomialPencil
