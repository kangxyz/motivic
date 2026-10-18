/-
Copyright (c) 2026 Motivic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic

/-! # Independent public client

Use the Motivic public entry, its correspondence category and the canonical
Milnor group supplied by Aglib.
-/
@[expose] public noncomputable section

universe u

namespace MotivicClient

variable (k : Type u) [Field k]

/-- The package entry exports its correspondence category. -/
example : CategoryTheory.Category (Motivic.Cor k) := inferInstance

/-- The public degree-zero equivalence uses the original integral symbol quotient. -/
example : MilnorK.K k 0 ≃ₗ[ℤ] ℤ :=
  MilnorK.zeroEquiv k

end MotivicClient
