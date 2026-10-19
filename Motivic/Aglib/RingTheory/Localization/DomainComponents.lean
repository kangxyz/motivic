/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Disjoint components from domain localizations

Two minimal primes below the same prime agree whenever localization at that
prime is a domain. Consequently a ring whose prime localizations are domains
has pairwise disjoint irreducible components in its prime spectrum.
-/

@[expose] public section

section

universe u v

/-- In a domain localization, a minimal prime below the localization prime maps to zero. -/
theorem _root_.Ideal.minimalPrime_map_eq_bot_of_isDomain
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (S : Type v) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S p]
    [IsDomain S] {q : Ideal R} (hq : q ∈ minimalPrimes R) (hqp : q ≤ p) :
    q.map (algebraMap R S) = ⊥ := by
  have : q.IsPrime := hq.isPrime
  have hmem : q.map (algebraMap R S) ∈ minimalPrimes S := by
    change q.map (algebraMap R S) ∈ (⊥ : Ideal S).minimalPrimes
    rw [← Ideal.map_bot (f := algebraMap R S),
      IsLocalization.minimalPrimes_map p.primeCompl S,
      Set.mem_preimage, Ideal.under_map_of_isLocalizationAtPrime p hqp]
    exact hq
  simpa only [IsDomain.minimalPrimes_eq_singleton_bot S, Set.mem_singleton_iff] using hmem

/-- Distinct minimal primes cannot lie below a prime whose localization is a domain. -/
theorem _root_.Ideal.minimalPrimes_eq_of_le_prime_of_isDomain
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (S : Type v) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S p]
    [IsDomain S] {q r : Ideal R} (hq : q ∈ minimalPrimes R)
    (hr : r ∈ minimalPrimes R) (hqp : q ≤ p) (hrp : r ≤ p) : q = r := by
  have : q.IsPrime := hq.isPrime
  have : r.IsPrime := hr.isPrime
  rw [← Ideal.under_map_of_isLocalizationAtPrime (S := S) p hqp,
    ← Ideal.under_map_of_isLocalizationAtPrime (S := S) p hrp,
    _root_.Ideal.minimalPrime_map_eq_bot_of_isDomain p S hq hqp,
    _root_.Ideal.minimalPrime_map_eq_bot_of_isDomain p S hr hrp]

/-- Domain localizations force any two intersecting irreducible components to coincide. -/
theorem _root_.PrimeSpectrum.irreducibleComponents_eq_of_mem_of_domain_localizations
    {R : Type u} [CommRing R]
    (hR : ∀ p : PrimeSpectrum R, IsDomain (Localization.AtPrime p.asIdeal))
    {Z W : Set (PrimeSpectrum R)} (hZ : Z ∈ irreducibleComponents (PrimeSpectrum R))
    (hW : W ∈ irreducibleComponents (PrimeSpectrum R))
    {x : PrimeSpectrum R} (hxZ : x ∈ Z) (hxW : x ∈ W) : Z = W := by
  rw [← PrimeSpectrum.zeroLocus_minimalPrimes] at hZ hW
  obtain ⟨q, hq, rfl⟩ := hZ
  obtain ⟨r, hr, rfl⟩ := hW
  have : IsDomain (Localization.AtPrime x.asIdeal) := hR x
  have hqr : q = r := _root_.Ideal.minimalPrimes_eq_of_le_prime_of_isDomain x.asIdeal
    (Localization.AtPrime x.asIdeal) hq hr hxZ hxW
  rw [hqr]

end
