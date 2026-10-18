/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulCycleReplacement
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Consumers of actual fixed-support Koszul replacement

Besides the literal prime-filtration telescope, these consumers check a
module with a generic prime-quotient summand and a strictly smaller support
summand. The latter disappears by proved dimension vanishing after the next
Koszul intersection. Its generic localized multiplicity is computed as zero,
while the generic summand has length one.
-/

@[expose] public section

open CategoryTheory Motivic.Koszul Motivic.LengthEuler Module
open scoped TensorProduct

universe u

namespace MotivicTest.KoszulCycleReplacement

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsLocalRing R] in
/-- An arbitrary actual complete prime filtration telescopes the literal
all-degree coefficient-complex Euler characteristic. -/
theorem actualFiltration (M : ModuleCat R) [Module.Finite R M]
    (D : Module.PrimeFiltrationFrom M ⊥) (s : List R) (J : Ideal R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ J))] (hJ : J ≤ Module.annihilator R M) :
    chainEuler (coefficientComplex M s)
        (finiteHomology_of_artinian_quotient_of_le_annihilator M s J hJ) =
      (D.primes.map (fixedSupportPrimeEuler s J)).sum :=
  primeFiltration_chainEuler_eq_sum M D s J hJ _

/-- Lower-dimensional prime factors are killed using actual remaining
Koszul equations under the fixed-support Artinian hypothesis. -/
theorem lowerPrimeContribution (s : List R) (p q : Ideal R) [p.IsPrime] [q.IsPrime]
    (hpq : p < q) [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ p))]
    (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R) :
    fixedSupportPrimeEuler s p q = 0 := by
  apply fixedSupportPrimeEuler_zero_of_not_minimal s p q hs hpq.le
  rw [Ideal.minimalPrimes_eq_subsingleton_self]
  simpa only [Set.mem_singleton_iff] using hpq.ne.symm

omit [IsLocalRing R] in
/-- The mixed module really has generic multiplicity one. Its additional
strict containing-ideal quotient summand has zero localized length. -/
theorem mixedGenericLength (p q : Ideal R) [p.IsPrime] (hpq : p < q)
    (hJ : p ≤ Module.annihilator R ((R ⧸ p) × (R ⧸ q)))
    (hp : p ∈ p.minimalPrimes) :
    fixedSupportGenericLength (ModuleCat.of R ((R ⧸ p) × (R ⧸ q))) p hJ ⟨p, hp⟩ = 1 := by
  have he := (TensorProduct.prodRight R (Localization.AtPrime p) (Localization.AtPrime p)
    (R ⧸ p) (R ⧸ q)).length_eq
  have hpone := Module.localized_primeQuotient_length p p (fun _ => rfl)
  have hqzero := Module.localized_primeQuotient_length p q (fun h => (hpq.not_ge h).elim)
  simp at hpone
  rw [ite_eq_right hpq.ne.symm] at hqzero
  simp only [Module.length_prod, hpone, hqzero, add_zero] at he
  simp only [fixedSupportGenericLength, integerLength, he, ENat.toNat_one, Nat.cast_one]

/-- Fixed-J replacement on a genuine mixed module discards its strictly
lower-dimensional summand only after applying the actual Koszul Euler law.
Neither coefficient module nor its chain terms are assumed finite length. -/
theorem mixedSupportReplacement (s : List R) (p q : Ideal R) [p.IsPrime] [q.IsPrime]
    (hpq : p < q)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ p))]
    (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R) :
    Nontrivial (R ⧸ q) ∧ ∃ h : FiniteHomology
        (coefficientComplex (ModuleCat.of R ((R ⧸ p) × (R ⧸ q))) s),
      chainEuler (coefficientComplex (ModuleCat.of R ((R ⧸ p) × (R ⧸ q))) s) h =
        chainEuler (coefficientComplex (ModuleCat.of R (R ⧸ p)) s)
          (fixedSupport_prime_finiteHomology s p p le_rfl) := by
  refine ⟨inferInstance, ?_⟩
  let M := ModuleCat.of R ((R ⧸ p) × (R ⧸ q))
  have hJ : p ≤ Module.annihilator R M := by
    change p ≤ Module.annihilator R ((R ⧸ p) × (R ⧸ q))
    rw [Module.annihilator_prod, Ideal.annihilator_quotient, Ideal.annihilator_quotient]
    exact le_inf le_rfl hpq.le
  have hp : p ∈ p.minimalPrimes := by rw [Ideal.minimalPrimes_eq_subsingleton_self]; simp
  let p₀ : p.minimalPrimes := ⟨p, hp⟩
  have hunique (x : p.minimalPrimes) : x = p₀ := by
    apply Subtype.ext
    have hx := x.2
    simpa only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] using hx
  refine ⟨finiteHomology_of_artinian_quotient_of_le_annihilator M s p hJ, ?_⟩
  rw [fixedSupport_chainEuler_replacement M s p hs hJ,
    finsum_eq_single _ p₀ (fun x hx => (hx (hunique x)).elim)]
  rw [mixedGenericLength p q hpq hJ hp, one_mul]

end MotivicTest.KoszulCycleReplacement
