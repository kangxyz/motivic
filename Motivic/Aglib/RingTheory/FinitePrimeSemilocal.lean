/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!
# Semilocalization at finitely many prime ideals

Localizing away from a finite union of prime ideals gives a ring with finitely
many maximal ideals. The primes need not be maximal or pairwise incomparable,
and no Noetherian hypothesis is required.
-/

@[expose] public section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- Prime avoidance for an ideal disjoint from the intersection of finitely many
prime complements. This includes the empty family. -/
theorem exists_le_of_disjoint_iInf_primeCompl (s : Finset (PrimeSpectrum R))
    {I : Ideal R}
    (hI : Disjoint ((⨅ p : s, p.1.asIdeal.primeCompl : Submonoid R) : Set R) I) :
    ∃ p ∈ s, I ≤ p.asIdeal := by
  classical
  have hsubset : (I : Set R) ⊆ ⋃ p ∈ (s : Set (PrimeSpectrum R)), (p.asIdeal : Set R) := by
    intro x hx
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    by_contra h
    apply Set.disjoint_left.mp hI ?_ hx
    exact Submonoid.mem_iInf.mpr fun p hp ↦ h ⟨p.1, p.2, hp⟩
  rcases s.eq_empty_or_nonempty with hs | ⟨p, hp⟩
  · have hzero := hsubset I.zero_mem
    simp [hs] at hzero
  · exact (Ideal.subset_union_prime p p (fun q _ _ _ ↦ q.isPrime)).mp hsubset

end Ideal

namespace IsLocalization

variable {R : Type*} [CommRing R] (s : Finset (PrimeSpectrum R))
variable (A : Type*) [CommRing A] [Algebra R A]
variable [IsLocalization (⨅ p : s, p.1.asIdeal.primeCompl) A]

/-- A maximal ideal of the localization away from a finite family of primes
contracts to one of those primes. -/
theorem exists_under_eq_of_isMaximal_iInf_primeCompl (m : MaximalSpectrum A) :
    ∃ p ∈ s, m.asIdeal.under R = p.asIdeal := by
  let S : Submonoid R := ⨅ p : s, p.1.asIdeal.primeCompl
  have hdisj : Disjoint (S : Set R) (m.asIdeal.under R) :=
    (IsLocalization.isPrime_iff_isPrime_disjoint S A m.asIdeal).mp m.isMaximal.isPrime |>.2
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_of_disjoint_iInf_primeCompl s hdisj
  have hpdisj : Disjoint (S : Set R) (p.asIdeal : Set R) := by
    apply Set.disjoint_left.mpr
    intro x hx hxp
    exact (Submonoid.mem_iInf.mp hx ⟨p, hp⟩) hxp
  have hprime : (p.asIdeal.map (algebraMap R A)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint S A p.asIdeal p.isPrime hpdisj
  have hmap : m.asIdeal = p.asIdeal.map (algebraMap R A) := by
    apply m.isMaximal.eq_of_le hprime.ne_top
    rw [← IsLocalization.map_under S A m.asIdeal]
    exact Ideal.map_mono hle
  refine ⟨p, hp, ?_⟩
  rw [hmap]
  exact IsLocalization.under_map_of_isPrime_disjoint S A p.isPrime hpdisj

include s in
/-- Every localization at the intersection of finitely many prime complements
has finite maximal spectrum. -/
theorem finite_maximalSpectrum_iInf_primeCompl : Finite (MaximalSpectrum A) := by
  classical
  let f : MaximalSpectrum A → Ideal R := fun m ↦ m.asIdeal.under R
  have hf : Function.Injective f := by
    intro m n h
    apply MaximalSpectrum.ext
    exact (IsLocalization.orderEmbedding (⨅ p : s, p.1.asIdeal.primeCompl) A).injective h
  apply (Set.finite_range_iff hf).mp
  apply (s.finite_toSet.image PrimeSpectrum.asIdeal).subset
  rintro _ ⟨m, rfl⟩
  obtain ⟨p, hp, heq⟩ := exists_under_eq_of_isMaximal_iInf_primeCompl s A m
  exact ⟨p, hp, heq.symm⟩

end IsLocalization

namespace Localization

variable {R : Type*} [CommRing R]

/-- The concrete localization away from finitely many prime ideals is semilocal. -/
theorem finite_maximalSpectrum_iInf_primeCompl (s : Finset (PrimeSpectrum R)) :
    Finite (MaximalSpectrum (Localization (⨅ p : s, p.1.asIdeal.primeCompl))) :=
  IsLocalization.finite_maximalSpectrum_iInf_primeCompl s _

end Localization
