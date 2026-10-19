/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Sheaves.IntegralAffineSheafIso
public import Motivic.Aglib.AlgebraicGeometry.Stalk.Dimension.StalkRankZero

/-! # Actual integral affine neighborhoods at a smooth rank-zero point -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.SmoothSite
variable {k : Type u} [Field k]

/-- Every original smooth point has an actual integral affine open neighborhood.
This uses the native open component cover followed by its actual affine cover. -/
theorem exists_integral_affine_open (X : SmoothSite (Spec (.of k))) (x : X.left) :
    ∃ O : X.left.Opens, IsAffineOpen O ∧ x ∈ O ∧ IsIntegral O.toScheme := by
  let C := integralAffineCover k X
  obtain ⟨i, y, hy⟩ := C.exists_eq x
  let O := (C.f i).opensRange
  have hx : x ∈ O := ⟨y, hy⟩
  let : Nonempty O.toScheme := ⟨⟨x, hx⟩⟩
  have hi : IsIntegral O.toScheme :=
    isIntegral_of_isOpenImmersion (C.f i).isoOpensRange.inv
  exact ⟨O, isAffineOpen_opensRange (C.f i), hx, hi⟩

end AlgebraicGeometry.Scheme.SmoothSite
