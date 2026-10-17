/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Aglib.AlgebraicGeometry.Morphisms.Etale.StalkMap

/-! # Strict local rank decrease at proper generizations -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A proper generization has strictly smaller finite local rank. -/
theorem stalk_rank_lt_of_proper_generization {X : Scheme} {x y : X}
    (h : y ⤳ x) (hne : y ≠ x) (d : ℕ)
    (hd : ringKrullDim (X.presheaf.stalk x) = d) :
    ringKrullDim (X.presheaf.stalk y) < d := by
  rw [ringKrullDim_stalk_eq_coheight] at hd ⊢
  have hlt : x < y := ⟨h, fun hxy => hne (h.antisymm hxy).eq⟩
  have hle := Order.coheight_anti hlt.le
  have hx : Order.coheight x = (d : ℕ∞) := WithBot.coe_eq_coe.mp hd
  have hy : Order.coheight y < ⊤ := lt_of_le_of_lt hle (by simp [hx])
  exact hd ▸ WithBot.coe_lt_coe.mpr (Order.coheight_strictAnti hlt hy)

end AlgebraicGeometry.Scheme
