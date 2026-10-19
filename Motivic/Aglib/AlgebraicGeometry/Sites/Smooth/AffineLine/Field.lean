/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Torus
public import Motivic.Aglib.AlgebraicGeometry.Cycles.FundamentalSupport
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Endpoints.FiniteFlatCurveSpecialization

/-!
# Affine lines over field-valued smooth sites
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators Polynomial

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.AffineLineField

variable (k : Type u) [Field k]

/-- The literal affine parameter line with its polynomial structure map. -/
def line : SmoothSite (Spec (.of k)) := by
  let : Algebra.Smooth k k[X] := {}
  have : Smooth (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr inferInstance
  exact mk (Spec.map (CommRingCat.ofHom Polynomial.C))

/-- The field point as an object of the smooth site. -/
abbrev point : SmoothSite (Spec (.of k)) := base (Spec (.of k))

/-- Evaluation at a scalar, with its literal affine-spectrum map. -/
def evaluationPoint (a : k) : point k ⟶ line k :=
  homMk (FiniteFlatCurve.endpoint a) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 (Spec (.of k))
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    exact Polynomial.eval_C)

instance lineIntegral : IsIntegral (line k).left :=
  inferInstanceAs (IsIntegral (Spec (.of k[X])))

instance pointIntegral : IsIntegral (point k).left :=
  inferInstanceAs (IsIntegral (Spec (.of k)))

instance lineIrreducible : IrreducibleSpace (line k).left :=
  inferInstanceAs (IrreducibleSpace (Spec (.of k[X])))

instance pointIrreducible : IrreducibleSpace (point k).left :=
  inferInstanceAs (IrreducibleSpace (Spec (.of k)))

variable {k}

/-- The literal line-target ambient product. -/
abbrev ambient (Y : SmoothSite (Spec (.of k))) : Scheme.{u} :=
  pullback (line k).hom Y.hom

/-- The original reduced support of an actual generic component. -/
abbrev componentSupport {P : Scheme.{u}} (z : genericPoints P) :=
  IntegralClosedSubscheme.pointClosure z.val

end AlgebraicGeometry.Scheme.SmoothSite.AffineLineField
