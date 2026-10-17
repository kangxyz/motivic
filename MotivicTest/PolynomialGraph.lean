/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.MvPolynomial.Graph
public import Mathlib.Data.ZMod.Basic

/-!
# Polynomial graph consumers over nonreduced and disconnected bases

The graph equations remain regular over `ZMod 4` and a product of fields; the
coefficient ring need not be reduced, a domain, or local. A zero ring still
admits the weak-regularity statement, without a false proper-quotient claim.
-/

@[expose] public noncomputable section

open RingTheory.Sequence
open Motivic.PolynomialGraph

namespace Motivic.MotivicTest.PolynomialGraph

/-- Arbitrary values over the nonreduced ring of integers modulo four. -/
theorem nonreduced_regular (n : ℕ) (c : Fin n → ZMod 4) :
    IsRegular (MvPolynomial (Fin n) (ZMod 4))
      ((List.finRange n).map (difference c)) := by
  have : Fact (1 < 4) := ⟨by decide⟩
  exact isRegular_differences c (List.finRange n) (List.nodup_finRange n)

/-- A disconnected coefficient spectrum does not affect graph regularity. -/
theorem disconnected_regular (n : ℕ) (c : Fin n → ℚ × ℚ) :
    IsRegular (MvPolynomial (Fin n) (ℚ × ℚ))
      ((List.finRange n).map (difference c)) :=
  isRegular_differences c (List.finRange n) (List.nodup_finRange n)

/-- The complete nonreduced graph ideal is the literal evaluation kernel. -/
theorem nonreduced_kernel (n : ℕ) (c : Fin n → ZMod 4) :
    RingHom.ker (evaluation c) = Ideal.ofList ((List.finRange n).map (difference c)) :=
  ker_evaluation_eq_ofList c (List.finRange n) List.mem_finRange

/-- The quotient retains the nilpotents of the original coefficient ring. -/
def nonreducedQuotient (n : ℕ) (c : Fin n → ZMod 4) :
    (MvPolynomial (Fin n) (ZMod 4) ⧸ ideal c) ≃ₐ[ZMod 4] ZMod 4 :=
  quotientEquiv c

/-- No nonzero-base assumption is imposed on weak regularity. -/
theorem zero_ring_weaklyRegular (n : ℕ) (c : Fin n → ZMod 1) :
    IsWeaklyRegular (MvPolynomial (Fin n) (ZMod 1))
      ((List.finRange n).map (difference c)) :=
  isWeaklyRegular_differences c (List.finRange n) (List.nodup_finRange n)

end Motivic.MotivicTest.PolynomialGraph
