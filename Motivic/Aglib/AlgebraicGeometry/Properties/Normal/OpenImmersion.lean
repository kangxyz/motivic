/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Normal stalks along open immersions

Normal-domain stalks pass through the actual open-immersion stalk isomorphisms,
without a global integrality or nonempty-source premise.

Intended upstream module: `Aglib.AlgebraicGeometry.Properties.Normal.OpenImmersion`.
Current consumer: the normal-stalk assertions for the original relative affine-line
compactification and its already selected coefficient restrictions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Normal-domain stalks restrict along the actual open-immersion stalk isomorphisms. -/
theorem NormalStalks.of_isOpenImmersion {X Y : Scheme.{u}} (hX : NormalStalks X)
    (f : Y ⟶ X) [IsOpenImmersion f] : NormalStalks Y := by
  intro y
  let := (hX (f y)).1
  let := (hX (f y)).2
  let e := (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

end AlgebraicGeometry.Scheme
