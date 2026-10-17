/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.TorsionFreeBaseChange
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Minimal primes of a flat scalar extension of a torsion-free algebra

A minimal prime of an algebra torsion-free over a domain contracts to zero.
Consequently the same holds after flat scalar extension to another domain.
The tensor algebra is the actual, possibly nonreduced algebra: no reduction,
finiteness, Noetherianity, or flatness of the original support algebra is used.
-/

@[expose] public section

open scoped TensorProduct

namespace Ideal

variable {R S B : Type*}

/-- Every minimal prime of an algebra torsion-free over a domain contracts to zero. -/
theorem under_eq_bot_of_mem_minimalPrimes_of_isTorsionFree
    [CommRing R] [CommRing B] [Algebra R B] [IsDomain R]
    [Module.IsTorsionFree R B] {q : Ideal B} (hq : q ∈ minimalPrimes B) :
    q.under R = ⊥ := by
  apply le_bot_iff.mp
  intro r hr
  apply Ideal.mem_bot.mpr
  by_contra hr0
  have hreg : algebraMap R B r ∈ nonZeroDivisors B := by
    rw [mem_nonZeroDivisors_iff_right]
    intro b hb
    have hs : r • b = 0 := by simpa only [Algebra.smul_def, mul_comm] using hb
    exact (smul_eq_zero.mp hs).resolve_left hr0
  exact Set.disjoint_left.mp
    (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hq) hr hreg

/-- Minimal primes of the whole tensor algebra contract to zero after flat scalar
extension between domains. The original algebra need only be torsion-free. -/
theorem under_eq_bot_of_mem_minimalPrimes_tensorProduct
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
    [IsDomain R] [IsDomain S] [Module.Flat R S] [Module.IsTorsionFree R B]
    {q : Ideal (S ⊗[R] B)} (hq : q ∈ minimalPrimes (S ⊗[R] B)) :
    q.under S = ⊥ := by
  let := Module.torsionFree_baseChange (R := R) (S := S) B
  exact under_eq_bot_of_mem_minimalPrimes_of_isTorsionFree hq

end Ideal
