/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Motivic.RingTheory.Smooth.Reduced

/-!
# Reduced sources of smooth morphisms over integral bases

For every source point, a genuine standard-smooth affine chart has a domain
as coefficient ring, because its base open is nonempty in an integral scheme.
The chart ring is reduced by étale polynomial coordinates. Reducedness passes
to its local rings, hence to every source stalk and the whole source scheme.
In particular every scheme smooth over an arbitrary field is reduced. Neither
connectedness nor irreducibility of the source is assumed or concluded.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic

/-- Smooth morphisms with integral target have reduced source. The proof is
local on the source and does not require a Noetherian or perfect base. -/
theorem isReduced_of_smooth_of_isIntegral {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f] [IsIntegral Y] : IsReduced X := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    obtain ⟨U, _, V, hV, hx, e, hf⟩ := Smooth.exists_isStandardSmooth f x
    have : Nonempty U := ⟨⟨f x, e hx⟩⟩
    have : _root_.IsReduced Γ(X, V) :=
      isReduced_of_isStandardSmooth (f.appLE U V e).hom hf
    have : IsReduced V := isReduced_of_isOpenImmersion hV.isoSpec.hom
    have : _root_.IsReduced (V.toScheme.presheaf.stalk ⟨x, hx⟩) :=
      isReduced_stalk_of_isReduced V.toScheme ⟨x, hx⟩
    exact isReduced_of_injective (V.stalkIso ⟨x, hx⟩).inv.hom
      (V.stalkIso ⟨x, hx⟩).symm.commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk X

/-- Every scheme smooth over an arbitrary field is reduced. -/
theorem isReduced_of_smooth_over_field (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [Smooth f] : IsReduced X :=
  isReduced_of_smooth_of_isIntegral f

end Motivic
