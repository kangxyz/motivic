/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulDimensionVanishing
public import Motivic.Algebra.Homology.KoszulPrimeFiltrationEuler
public import Motivic.RingTheory.LocalLength.FixedSupportMultiplicity
public import Motivic.RingTheory.LocalLength.StrictPrimeDimension
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Fixed-support replacement for actual Koszul Euler characteristics

A fixed ideal contained in the coefficient annihilator gives one common
minimal-prime index set. Actual prime-filtration additivity, strict-prime
dimension drop, and Koszul dimension vanishing remove the nongeneric factors.
The remaining multiplicities are actual finite localized module lengths.
-/

@[expose] public section

open CategoryTheory Motivic.LengthEuler Motivic.LocalLength
open scoped TensorProduct

universe u

namespace Motivic.Koszul

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- A nongeneric prime containing the fixed support has dimension strictly
smaller than the number of equations. The numerical upper bound is derived
from Artinianness, rather than supplied as an expected-dimension assumption. -/
theorem fixedSupport_nonminimal_dimension_lt (s : List R) (J q : Ideal R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ J))]
    (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R)
    [q.IsPrime] (hJq : J ≤ q) (hq : q ∉ J.minimalPrimes) :
    Module.supportDim R (R ⧸ q) < s.length := by
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le hJq
  have : p.IsPrime := hp.isPrime
  have hstrict : p < q := lt_of_le_of_ne hpq (fun he => hq (he ▸ hp))
  have hdim := strictPrime_support_dimension p q hstrict
  have hbound := koszulDimension_quotient_le_length J s hs
  have hle : Module.supportDim R (R ⧸ p) ≤ Module.supportDim R (R ⧸ J) := by
    simp only [Module.supportDim_quotient_eq_ringKrullDim]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hp.le)
      (Ideal.Quotient.factor_surjective hp.le)
  exact ENat.WithBot.add_one_le_natCast_iff.mp (hdim.trans (hle.trans hbound))

/-- Every nongeneric filtration prime has zero genuine Koszul Euler
contribution, even for mixed-dimensional fixed support. -/
theorem fixedSupportPrimeEuler_zero_of_not_minimal (s : List R) (J q : Ideal R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ J))]
    (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R)
    [q.IsPrime] (hJq : J ≤ q) (hq : q ∉ J.minimalPrimes) :
    fixedSupportPrimeEuler s J q = 0 := by
  have : IsArtinianRing (R ⧸ (Ideal.ofList s ⊔
      Module.annihilator R (ModuleCat.of R (R ⧸ q)))) := by
    change IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ Module.annihilator R (R ⧸ q)))
    rw [Ideal.annihilator_quotient]
    exact koszulDimension_artinian_quotient_of_le _ _ (sup_le_sup_left hJq _)
  rw [fixedSupportPrimeEuler_eq s J q hJq
    (finiteHomology_of_artinian_support_quotient _ _)]
  exact koszulDimension_chainEuler_zero _ s hs
    (fixedSupport_nonminimal_dimension_lt s J q hs hJq hq)

/-- Actual filtration Euler length regroups on the fixed minimal-prime set;
the discarded summands vanish by dimension, not by a support-cycle convention. -/
theorem fixedSupport_chainEuler_eq_count_sum (M : ModuleCat R) [Module.Finite R M]
    (D : PrimeFiltrationFrom M ⊥) (s : List R) (J : Ideal R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ J))]
    (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R) (hJ : J ≤ Module.annihilator R M)
    (hM : FiniteHomology (coefficientComplex M s)) :
    chainEuler (coefficientComplex M s) hM =
      ∑ᶠ p : J.minimalPrimes, (D.primes.count p.1 : ℤ) * fixedSupportPrimeEuler s J p.1 := by
  classical
  let hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing R J
  let : Fintype J.minimalPrimes := hfin.fintype
  rw [finsum_eq_sum_of_fintype, primeFiltration_chainEuler_eq_sum M D s J hJ hM]
  have hlist := Finset.sum_list_map_count D.primes (fixedSupportPrimeEuler s J)
  simp only [nsmul_eq_mul] at hlist
  rw [hlist]
  refine Eq.trans ?_ (Finset.sum_subtype hfin.toFinset
    (fun q : Ideal R => hfin.mem_toFinset (a := q))
    (fun q => (D.primes.count q : ℤ) * fixedSupportPrimeEuler s J q))
  apply Finset.sum_congr_of_eq_on_inter
  · intro q hq hnot
    have hmem : q ∈ D.primes := List.mem_toFinset.mp hq
    have : q.IsPrime := D.primes_isPrime q hmem
    have hle := hJ.trans (Module.annihilator_le_of_mem_support (D.prime_mem_support q hmem))
    rw [fixedSupportPrimeEuler_zero_of_not_minimal s J q hs hle
      (fun h => hnot (hfin.mem_toFinset.mpr h)), mul_zero]
  · intro q _ hnot
    rw [List.count_eq_zero.mpr (fun h => hnot (List.mem_toFinset.mpr h))]
    simp
  · intro _ _ _
    rfl

/-- The coefficient at a fixed generic point is the actual finite localized
length of the original module. Finiteness is proved before integer conversion. -/
noncomputable def fixedSupportGenericLength (M : ModuleCat R) [Module.Finite R M]
    (J : Ideal R) (hJ : J ≤ Module.annihilator R M) (p : J.minimalPrimes) : ℤ := by
  letI : p.1.IsPrime := p.2.isPrime
  exact integerLength (R := Localization.AtPrime p.1) (Localization.AtPrime p.1 ⊗[R] M)
    (fixedSupport_localized_length_ne_top M J hJ p.1 p.2)

omit [IsLocalRing R] in
/-- The fixed-support multiplicity agrees with literal prime-filtration count. -/
theorem fixedSupportGenericLength_eq_count (M : ModuleCat R) [Module.Finite R M]
    (D : PrimeFiltrationFrom M ⊥) (J : Ideal R) (hJ : J ≤ Module.annihilator R M)
    (p : J.minimalPrimes) : fixedSupportGenericLength M J hJ p = D.primes.count p.1 := by
  let : p.1.IsPrime := p.2.isPrime
  simp only [fixedSupportGenericLength, integerLength,
    D.fixedSupport_localized_length_eq_count J hJ p.1 p.2, ENat.toNat_natCast]

/-- Fixed-J replacement for the actual all-degree coefficient Koszul Euler
characteristic. No purity or supplied expected-dimension bound is assumed. -/
theorem fixedSupport_chainEuler_replacement (M : ModuleCat R) [Module.Finite R M]
    (s : List R) (J : Ideal R) [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ J))]
    (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R) (hJ : J ≤ Module.annihilator R M) :
    chainEuler (coefficientComplex M s)
        (finiteHomology_of_artinian_quotient_of_le_annihilator M s J hJ) =
      ∑ᶠ p : J.minimalPrimes, fixedSupportGenericLength M J hJ p *
        chainEuler (coefficientComplex (ModuleCat.of R (R ⧸ p.1)) s)
          (fixedSupport_prime_finiteHomology s J p.1 p.2.le) := by
  obtain ⟨D⟩ := nonempty_primeFiltration (A := R) M
  rw [fixedSupport_chainEuler_eq_count_sum M D s J hs hJ]
  apply finsum_congr
  intro p
  rw [fixedSupportGenericLength_eq_count M D J hJ p,
    fixedSupportPrimeEuler_eq s J p.1 p.2.le]

end Motivic.Koszul
