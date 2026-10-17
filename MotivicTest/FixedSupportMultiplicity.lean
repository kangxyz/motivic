/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.LocalLength.FixedSupportMultiplicity
public import Motivic.RingTheory.LocalLength.StrictPrimeDimension

/-!
# Consumers of fixed-support multiplicities and strict prime dimension

The fixed ideal may be strictly smaller than the coefficient annihilator.
A strict containing-prime quotient is an explicit absent generic component:
its localized length and its occurrence count at the fixed generic point
both vanish. The dimension consumer needs neither locality nor catenarity.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace MotivicTest.FixedSupportMultiplicity

open Motivic.LocalLength

variable {R : Type u} [CommRing R]

/-- The fixed-support generic coefficients are finite literal lengths. -/
theorem fixedSupportFinite [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (J : Ideal R) (hJ : J ≤ Module.annihilator R M)
    (p : Ideal R) [p.IsPrime] (hp : p ∈ J.minimalPrimes) :
    Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] M) ≠ ⊤ :=
  fixedSupport_localized_length_ne_top M J hJ p hp

/-- A larger annihilator can remove a generic point of the fixed support;
the literal filtration then records zero occurrences there. -/
theorem strictlySupportedQuotient (p q : Ideal R) [p.IsPrime] (hpq : p < q)
    (D : PrimeFiltrationFrom (R ⧸ q) ⊥) :
    Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] (R ⧸ q)) = 0 ∧
      D.primes.count p = 0 := by
  have hJ : p ≤ Module.annihilator R (R ⧸ q) := by
    rw [Ideal.annihilator_quotient]
    exact hpq.le
  have hp : p ∈ p.minimalPrimes := by rw [Ideal.minimalPrimes_eq_subsingleton_self]; simp
  have hnot : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∉ Module.support R (R ⧸ q) := by
    intro hs
    have hqp := Module.annihilator_le_of_mem_support hs
    rw [Ideal.annihilator_quotient] at hqp
    exact hpq.not_ge hqp
  exact ⟨D.fixedSupport_localized_length_zero_of_not_mem_support p hJ p hp hnot,
    D.fixedSupport_count_zero_of_not_mem_support p hnot⟩

/-- A strict containing-prime quotient is smaller dimensional without any
Noetherian, local, catenary, or expected-dimension input. -/
theorem strictSupportDrop (p q : Ideal R) [p.IsPrime] (hpq : p < q) :
    Module.supportDim R (R ⧸ q) + 1 ≤ Module.supportDim R (R ⧸ p) :=
  strictPrime_support_dimension p q hpq

end MotivicTest.FixedSupportMultiplicity
