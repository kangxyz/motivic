/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.GoingDown

/-! # Minimal primes over an extended ideal contract under going down -/

@[expose] public section

namespace Ideal

universe u v

/-- Going down preserves minimality over the actual original ideal, not merely
minimality of the ambient ring. Flat scalar extension is the intended consumer. -/
theorem under_mem_minimalPrimes_of_hasGoingDown
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.HasGoingDown R S] (I : Ideal R) (Q : Ideal S)
    (hQ : Q ∈ (I.map (algebraMap R S)).minimalPrimes) :
    Q.under R ∈ I.minimalPrimes := by
  let : Q.IsPrime := hQ.isPrime
  refine ⟨⟨inferInstance, Ideal.map_le_iff_le_comap.mp hQ.le⟩, ?_⟩
  intro p hp hpQ
  let : p.IsPrime := hp.1
  obtain ⟨P, hPQ, hP, hPp⟩ :=
    Q.exists_ideal_le_liesOver_of_le (p := p) (q := Q.under R) hpQ
  let : P.IsPrime := hP
  let : P.LiesOver p := hPp
  have hIP : I.map (algebraMap R S) ≤ P := by
    apply Ideal.map_le_iff_le_comap.mpr
    exact hp.2.trans_eq (P.over_def p)
  have hQP : Q ≤ P := hQ.2 ⟨hP, hIP⟩ hPQ
  rw [show Q = P from le_antisymm hQP hPQ, ← P.over_def p]

end Ideal
