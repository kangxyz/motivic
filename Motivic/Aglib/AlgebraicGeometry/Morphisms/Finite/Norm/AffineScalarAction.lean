/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FiniteSchemeNormBaseChange

/-! # The original scalar action after the canonical affine target identification

Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.AffineScalarAction`.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.FiniteSchemeNormBaseChange

/-- Passing to the canonical Spec of an affine target preserves its literal
original global-sections ring map. No algebra structure or freeness is reselected. -/
theorem scalarMap_comp_isoSpec {T W : Scheme.{u}} [IsAffine W] (n : T ⟶ W) :
    scalarMap (n ≫ W.isoSpec.hom) = n.appTop.hom := by
  ext a
  change (n ≫ W.isoSpec.hom).appTop ((Scheme.ΓSpecIso Γ(W, ⊤)).inv a) = n.appTop a
  rw [Scheme.Hom.comp_appTop]
  change n.appTop (W.isoSpec.hom.appTop ((Scheme.ΓSpecIso Γ(W, ⊤)).inv a)) = n.appTop a
  simp only [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop, Iso.inv_hom_id_apply]

/-- The inverse canonical affine identification recovers the original coefficient,
not a coefficient for an independently chosen scalar action. -/
theorem isoSpec_inv_coefficient {W X : Scheme.{u}} [IsAffine W]
    (v : W ⟶ X) (c : Γ(X, ⊤)) :
    (Scheme.ΓSpecIso Γ(W, ⊤)).hom ((W.isoSpec.inv ≫ v).appTop c) = v.appTop c := by
  have h := congrArg (fun m : W ⟶ W => m.appTop (v.appTop c)) W.isoSpec.hom_inv_id
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.isoSpec_hom,
    Scheme.toSpecΓ_appTop, Scheme.Hom.id_appTop, CommRingCat.id_apply] using h

end AlgebraicGeometry.FiniteSchemeNormBaseChange
