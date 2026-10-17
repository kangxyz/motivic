/-
Copyright (c) 2026 Motivic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.KTheory.MilnorK.LowDegree

/-! # Independent public client

Use the original Milnor group and its exported degree-zero computation.
-/
@[expose] public noncomputable section

universe u

namespace MotivicClient

variable (k : Type u) [Field k]

/-- The public degree-zero equivalence uses the original integral symbol quotient. -/
example : Motivic.KTheory.MilnorK.K k 0 ≃ₗ[ℤ] ℤ :=
  Motivic.KTheory.MilnorK.zeroEquiv k

end MotivicClient
