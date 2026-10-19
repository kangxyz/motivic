/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Normal

/-! # Integral components as smooth-site objects

The canonical structure morphisms give the integral component objects and
their actual open-immersion inclusions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k]

/-- The actual open integral component, with its original structure morphism. -/
def integralComponent (X : SmoothSite (Spec (.of k)))
    (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left) :
    SmoothSite (Spec (.of k)) :=
  mk ((componentOpen k X Z hZ).ι ≫ X.hom)

instance integralComponent_isIntegral (X : SmoothSite (Spec (.of k)))
    (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left) :
    IsIntegral (integralComponent k X Z hZ).left :=
  isIntegral_componentOpen k X Z hZ

/-- The inclusion is the original open-subscheme map, not a chosen comparison. -/
def integralComponentι (X : SmoothSite (Spec (.of k)))
    (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left) :
    integralComponent k X Z hZ ⟶ X :=
  homMk (componentOpen k X Z hZ).ι rfl

instance integralComponentι_isOpenImmersion (X : SmoothSite (Spec (.of k)))
    (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left) :
    IsOpenImmersion (integralComponentι k X Z hZ).left :=
  inferInstanceAs (IsOpenImmersion (componentOpen k X Z hZ).ι)

end AlgebraicGeometry.Scheme.SmoothSite
