/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
/-! # Boundary values through an actual open factor

Equality on the whole inverse-image open gives equality on global sections
through the same boundary morphism factored through the chosen open.

Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.OpenImmersion.BoundarySections`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Pencils.NativeCorrectionNormAction`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- A value-one section on the full boundary has value one after passage to
global sections of any actual factor through the open. No nonemptiness or
reducedness assumption is used. -/
theorem appTop_eq_one_of_open_factor
    {E T : Scheme.{u}} (b : E ⟶ T) (V : T.Opens) (r : Γ(T, V))
    (β : E ⟶ V.toScheme) (hβ : β ≫ V.ι = b) (h : b.app V r = 1) :
    β.appTop (V.topIso.inv r) = 1 := by
  subst b
  have htop : V.topIso.inv = V.ι.appLE V ⊤ V.ι_preimage_self.ge := by
    simp only [Opens.topIso_inv, Opens.ι_appLE]
    apply congrArg
    exact Subsingleton.elim _ _
  have hβtop : β.appLE ⊤ ⊤ le_rfl = β.appTop := by
    simp [appLE]
  have hres : β.appTop (V.topIso.inv r) =
      (β ≫ V.ι).appLE V ⊤ (by simp) r := by
    rw [htop, ← CommRingCat.comp_apply]
    simpa only [hβtop] using
      congrArg (fun k : Γ(T, V) ⟶ Γ(E, ⊤) => k r)
        (appLE_comp_appLE β V.ι V ⊤ ⊤ V.ι_preimage_self.ge le_rfl)
  rw [hres]
  simp only [appLE, CommRingCat.comp_apply, h, map_one]

end AlgebraicGeometry.Scheme.Hom
