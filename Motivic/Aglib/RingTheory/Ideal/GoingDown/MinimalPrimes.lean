/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Ideal.MinimalPrime.GoingDown

/-!
# Going down preserves minimal primes

A minimal prime contracts to a minimal prime under a going-down algebra.
Over a domain its contraction is zero. The extension ring need not be a
domain or reduced, and the two rings may occupy independent universes.

The intended owner is `Aglib.RingTheory.Ideal.GoingDown.MinimalPrimes`.
These zero-ideal interfaces specialize the pinned upstream theorem
`Ideal.minimalPrime_map_under_of_goingDown`; the contraction is the actual
`Ideal.under` along `algebraMap`. `Tests.GenericDominance` consumes them
alongside the downstream generic-component dominance results.
-/

@[expose] public section

universe u v

namespace Ideal

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.HasGoingDown R S]

/-- Going down sends every actual minimal prime to an actual minimal prime. -/
theorem minimalPrime_under_of_goingDown (P : Ideal S) (hP : _root_.IsMinimalPrime P) :
    _root_.IsMinimalPrime (P.under R) := by
  apply minimalPrime_map_under_of_goingDown (⊥ : Ideal R) P
  rw [map_bot]
  exact hP

/-- Over a domain, every minimal component of a going-down algebra dominates
at the level of its generic prime, even when the algebra is nonreduced. -/
theorem minimalPrime_under_eq_bot_of_goingDown [IsDomain R]
    (P : Ideal S) (hP : P ∈ minimalPrimes S) : P.under R = ⊥ := by
  have h := minimalPrime_under_of_goingDown (R := R) P hP
  simpa only [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] using
    (show P.under R ∈ minimalPrimes R from h)

end Ideal
