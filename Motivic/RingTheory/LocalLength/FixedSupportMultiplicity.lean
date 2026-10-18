/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PrimeFiltration.Multiplicity
public import Aglib.RingTheory.FiniteLength.Support
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Support
public import Aglib.RingTheory.PrimeFiltration.Length
public import Aglib.RingTheory.PrimeFiltration.Support
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Filtration
public import Aglib.RingTheory.PrimeFiltration.Primes
public import Aglib.RingTheory.Length.ExactSequence
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Additivity
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Basic
public import Aglib.RingTheory.ScalarHomology.Basic
public import Aglib.RingTheory.PrimeFiltration.Basic

/-!
# Prime-filtration multiplicities on one fixed support

An ideal contained in the annihilator fixes the generic index set uniformly
for all coefficient modules. At each minimal prime of that ideal, the actual
localized length is the occurrence count in any complete prime filtration.
The length is finite, including when the module vanishes at that prime.

Aglib migration adaptation: downstream filtration methods use explicit
qualified calls because the filtration now has its native Module owner.
Statements and hypotheses are unchanged.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Module.PrimeFiltrationFrom

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-- At a minimal prime of a fixed annihilating support ideal, every surviving
filtration factor is that prime. The resulting actual local length is its
literal occurrence count. -/
theorem fixedSupport_localized_length_eq_count (D : Module.PrimeFiltrationFrom (A := A) M ⊥)
    (J : Ideal A) (hJ : J ≤ Module.annihilator A M)
    (p : Ideal A) [p.IsPrime] (hp : p ∈ J.minimalPrimes) :
    Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] M) =
      (D.primes.count p : ℕ∞) := by
  classical
  rw [D.length_baseChange_eq_add_sum (Localization.AtPrime p), Module.length_eq_zero, zero_add]
  have hfactor (q : Ideal A) (hq : q ∈ D.primes) :
      Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] (A ⧸ q)) =
        if q = p then 1 else 0 := by
    apply Module.localized_primeQuotient_length p q
    intro hqp
    exact hqp.antisymm (hp.2 ⟨D.primes_isPrime q hq,
      hJ.trans (Module.annihilator_le_of_mem_support (D.prime_mem_support q hq))⟩ hqp)
  rw [List.map_congr_left hfactor]
  induction D.primes with
  | nil => simp
  | cons q qs ih =>
    by_cases hqp : q = p
    · subst q
      simpa [add_comm] using congrArg (fun x : ℕ∞ => x + 1) ih
    · simpa [hqp] using ih

/-- The generic coefficient is finite before converting its extended natural
length to an integer or natural number. -/
theorem fixedSupport_localized_length_ne_top (D : Module.PrimeFiltrationFrom (A := A) M ⊥)
    (J : Ideal A) (hJ : J ≤ Module.annihilator A M)
    (p : Ideal A) [p.IsPrime] (hp : p ∈ J.minimalPrimes) :
    Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] M) ≠ ⊤ := by
  rw [Module.PrimeFiltrationFrom.fixedSupport_localized_length_eq_count D J hJ p hp]
  exact ENat.natCast_ne_top _

/-- A prime outside the actual coefficient support occurs zero times, even
when it is a generic point of the larger fixed support. -/
theorem fixedSupport_count_zero_of_not_mem_support (D : Module.PrimeFiltrationFrom (A := A) M ⊥)
    (p : Ideal A) [p.IsPrime] (hp : (⟨p, inferInstance⟩ : PrimeSpectrum A) ∉ Module.support A M) :
    D.primes.count p = 0 := by
  classical
  apply List.count_eq_zero.mpr
  exact fun hmem => hp (D.prime_mem_support p hmem)

/-- Both sides of the fixed-support multiplicity formula vanish outside
actual coefficient support. -/
theorem fixedSupport_localized_length_zero_of_not_mem_support
    (D : Module.PrimeFiltrationFrom (A := A) M ⊥)
    (J : Ideal A) (hJ : J ≤ Module.annihilator A M)
    (p : Ideal A) [p.IsPrime] (hp : p ∈ J.minimalPrimes)
    (hnot : (⟨p, inferInstance⟩ : PrimeSpectrum A) ∉ Module.support A M) :
    Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] M) = 0 := by
  rw [Module.PrimeFiltrationFrom.fixedSupport_localized_length_eq_count D J hJ p hp,
    Module.PrimeFiltrationFrom.fixedSupport_count_zero_of_not_mem_support D p hnot]
  rfl

end Module.PrimeFiltrationFrom

namespace Module

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- A finite module has finite localized length at every generic point of
any fixed support ideal contained in its annihilator. -/
theorem fixedSupport_localized_length_ne_top (J : Ideal A)
    (hJ : J ≤ Module.annihilator A M) (p : Ideal A) [p.IsPrime]
    (hp : p ∈ J.minimalPrimes) :
    Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] M) ≠ ⊤ := by
  obtain ⟨D⟩ := Module.nonempty_primeFiltration (A := A) M
  exact Module.PrimeFiltrationFrom.fixedSupport_localized_length_ne_top D J hJ p hp

end Module
