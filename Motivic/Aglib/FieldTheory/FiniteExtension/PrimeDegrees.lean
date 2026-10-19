/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Data.Nat.Prime.Basic

/-! # Two large prime extension degrees avoiding a fixed residue degree -/

@[expose] public section

namespace Nat

/-- Two distinct prime degrees exceed the avoidance bound and are each coprime
to the positive residue degree, as well as coprime to each other. -/
theorem exists_two_large_prime_degrees_coprime
    (e N : ℕ) (he : e ≠ 0) :
    ∃ n m : ℕ, n.Prime ∧ m.Prime ∧ N < n ∧ N < m ∧
      n ≠ m ∧ e.Coprime n ∧ e.Coprime m ∧ n.Coprime m := by
  obtain ⟨n, hn, hnprime⟩ := exists_infinite_primes (max e N + 1)
  obtain ⟨m, hm, hmprime⟩ := exists_infinite_primes (n + 1)
  have hen : e < n := lt_of_le_of_lt (le_max_left e N) (by omega)
  have hNn : N < n := lt_of_le_of_lt (le_max_right e N) (by omega)
  have hnm : n < m := by omega
  exact ⟨n, m, hnprime, hmprime, hNn, hNn.trans hnm, hnm.ne,
    (coprime_of_lt_prime he hen hnprime).symm,
    (coprime_of_lt_prime he (hen.trans hnm) hmprime).symm,
    (coprime_primes hnprime hmprime).mpr hnm.ne⟩

end Nat
