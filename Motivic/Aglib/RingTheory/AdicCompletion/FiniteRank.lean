/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.AdicCompletion.FiniteAlgebra
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Finite free rank of the actual completed algebra -/

@[expose] public noncomputable section

namespace AdicCompletion

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsNoetherianRing R] [Module.Finite R S] [Module.Free R S] [Nontrivial R]
  (I : Ideal R) [Nontrivial (AdicCompletion I R)]

/-- The actual completed algebra has the original finite free rank over the completed base. -/
theorem finrank_extendedCompletion :
    letI := extendedCompletionAlgebra (S := S) I
    Module.finrank (AdicCompletion I R) (AdicCompletion (I.map (algebraMap R S)) S) =
      Module.finrank R S := by
  let := extendedCompletionAlgebra (S := S) I
  rw [← (tensorEquivExtendedCompletionBase (S := S) I).toLinearEquiv.finrank_eq]
  exact Module.finrank_baseChange

end AdicCompletion
