/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.StalkRankGenerization

/-! # Zero local rank on an integral scheme identifies its original generic point -/

@[expose] public noncomputable section
open AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme

/-- On an integral scheme, zero dimension of the actual local ring means the
point is the actual generic point. -/
theorem eq_genericPoint_of_stalk_rank_zero {X : Scheme.{u}} [IsIntegral X]
    (x : X) (hx : ringKrullDim (X.presheaf.stalk x) = 0) : x = genericPoint X := by
  rw [ringKrullDim_stalk_eq_coheight] at hx
  have h : Order.coheight x = 0 := WithBot.coe_eq_coe.mp hx
  have hm := Order.coheight_eq_zero.mp h
  have hle : x ≤ genericPoint X := genericPoint_specializes x
  exact ((show genericPoint X ⤳ x from hle).antisymm (hm hle)).eq.symm

end AlgebraicGeometry.Scheme
