/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.HyperhomologyBounded
public import Motivic.Aglib.Algebra.Homology.Koszul.CycleReplacement

/-!
# Two-list replacement on the actual fixed Koszul support

The original finite coefficient module determines one support ideal from the
first equation list. Its actual homology modules are finite and annihilated
by that ideal. Bounded hyperhomology and fixed-support replacement therefore
express the actual total tensor Euler characteristic as one minimal-prime
sum, with coefficients the alternating finite localized lengths of the
first-stage homology. No finite-length hypothesis on the original terms or
intermediate homology is imposed. Geometric stalk and incidence comparisons
are separate from this local algebra identity.
-/

@[expose] public section

universe u

open CategoryTheory HomologicalComplex _root_.HomologicalComplex.ModuleLengthEuler

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The actual alternating generic length of the first-stage homology, on one
fixed support. Every localized length is finite before integer conversion. -/
noncomputable def twoListGenericEuler (M : ModuleCat R) [Module.Finite R M]
    (t : List R) (p : (Ideal.ofList t ⊔ Module.annihilator R M).minimalPrimes) : ℤ :=
  ∑ n : Fin (t.length + 1), (-1 : ℤ) ^ (n : ℕ) *
    fixedSupportGenericLength ((coefficientComplex M t).homology n)
      (Ideal.ofList t ⊔ Module.annihilator R M)
      (support_le_annihilator_coefficient_homology M t n) p

/-- Actual two-list replacement over a Noetherian local ring. The first-stage
coefficient module is explicitly finite; its length need not be finite. -/
theorem twoList_chainEuler_replacement [IsLocalRing R]
    (M : ModuleCat R) [Module.Finite R M] (s t : List R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔
      (Ideal.ofList t ⊔ Module.annihilator R M)))]
    (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R) :
    ∃ h : FiniteHomology (tensorObj (chainComplex s) (coefficientComplex M t)),
      chainEuler (tensorObj (chainComplex s) (coefficientComplex M t)) h =
        ∑ᶠ p : (Ideal.ofList t ⊔ Module.annihilator R M).minimalPrimes,
          twoListGenericEuler M t p *
            chainEuler (coefficientComplex (ModuleCat.of R (R ⧸ p.1)) s)
              (fixedSupport_prime_finiteHomology s
                (Ideal.ofList t ⊔ Module.annihilator R M) p.1 p.2.le) := by
  classical
  obtain ⟨h, he⟩ := coefficient_koszulTensor_chainEuler M s t
  refine ⟨h, ?_⟩
  have hLayer (n : Fin (t.length + 1)) :
      chainEuler (coefficientComplex ((coefficientComplex M t).homology n) s)
          (coefficient_homology_koszul_finiteHomology M s t n) =
        ∑ᶠ p : (Ideal.ofList t ⊔ Module.annihilator R M).minimalPrimes,
          fixedSupportGenericLength ((coefficientComplex M t).homology n)
              (Ideal.ofList t ⊔ Module.annihilator R M)
              (support_le_annihilator_coefficient_homology M t n) p *
            chainEuler (coefficientComplex (ModuleCat.of R (R ⧸ p.1)) s)
              (fixedSupport_prime_finiteHomology s
                (Ideal.ofList t ⊔ Module.annihilator R M) p.1 p.2.le) :=
    fixedSupport_chainEuler_replacement ((coefficientComplex M t).homology n) s
      (Ideal.ofList t ⊔ Module.annihilator R M) hs
      (support_le_annihilator_coefficient_homology M t n)
  let : Fintype (Ideal.ofList t ⊔ Module.annihilator R M).minimalPrimes :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing R
      (Ideal.ofList t ⊔ Module.annihilator R M)).fintype
  rw [he]
  simp_rw [hLayer, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [twoListGenericEuler, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  ring

end ChainComplex.Koszul
