/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulTwoListReplacement

/-!
# Consumers of actual two-list fixed-support replacement

These consumers check actual first-stage localized length finiteness, the
signed degree-one generic coefficient, a dependent first equation list, and
zero coefficients. The fixed prime index set is the same for every homology
module. Finite generation of the original coefficient module remains explicit.
-/

@[expose] public section

universe u

open CategoryTheory HomologicalComplex Motivic.Koszul Motivic.LengthEuler
open scoped TensorProduct

namespace MotivicTest.KoszulTwoListReplacement

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The literal localized first-stage homology has finite length at every
minimal prime of the one fixed support, in every degree. -/
theorem localizedHomologyLengthFinite (M : ModuleCat R) [Module.Finite R M]
    (t : List R) (n : ℕ) (p : Ideal R) [p.IsPrime]
    (hp : p ∈ (Ideal.ofList t ⊔ Module.annihilator R M).minimalPrimes) :
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[R] (coefficientComplex M t).homology n) ≠ ⊤ :=
  Module.fixedSupport_localized_length_ne_top
    ((coefficientComplex M t).homology n) _
    (support_le_annihilator_coefficient_homology M t n) p hp

/-- The actual one-equation generic coefficient retains both homology degrees
with the subtraction required by the total-complex grading. -/
theorem oneEquationGenericSign (M : ModuleCat R) [Module.Finite R M] (a : R)
    (p : (Ideal.ofList [a] ⊔ Module.annihilator R M).minimalPrimes) :
    twoListGenericEuler M [a] p =
      fixedSupportGenericLength ((coefficientComplex M [a]).homology 0)
          (Ideal.ofList [a] ⊔ Module.annihilator R M)
          (support_le_annihilator_coefficient_homology M [a] 0) p -
        fixedSupportGenericLength ((coefficientComplex M [a]).homology 1)
          (Ideal.ofList [a] ⊔ Module.annihilator R M)
          (support_le_annihilator_coefficient_homology M [a] 1) p := by
  simp [twoListGenericEuler, Fin.sum_univ_two, sub_eq_add_neg]

/-- A repeated pair followed by a zero equation requires no regularity of the
first list; all actual homology degrees enter the common-support coefficient. -/
theorem repeatedZeroFirstList [IsLocalRing R]
    (M : ModuleCat R) [Module.Finite R M] (s : List R) (a : R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔
      (Ideal.ofList [a, a, 0] ⊔ Module.annihilator R M)))]
    (hs : ∀ b ∈ s, b ∈ IsLocalRing.maximalIdeal R) :
    ∃ h : FiniteHomology (tensorObj (chainComplex s) (coefficientComplex M [a, a, 0])),
      chainEuler (tensorObj (chainComplex s) (coefficientComplex M [a, a, 0])) h =
        ∑ᶠ p : (Ideal.ofList [a, a, 0] ⊔ Module.annihilator R M).minimalPrimes,
          twoListGenericEuler M [a, a, 0] p *
            chainEuler (coefficientComplex (ModuleCat.of R (R ⧸ p.1)) s)
              (fixedSupport_prime_finiteHomology s
                (Ideal.ofList [a, a, 0] ⊔ Module.annihilator R M) p.1 p.2.le) :=
  twoList_chainEuler_replacement M s [a, a, 0] hs

/-- Empty first lists retain the same actual fixed-support replacement interface. -/
theorem emptyFirstList [IsLocalRing R]
    (M : ModuleCat R) [Module.Finite R M] (s : List R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔
      (Ideal.ofList [] ⊔ Module.annihilator R M)))]
    (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R) :
    ∃ h : FiniteHomology (tensorObj (chainComplex s) (coefficientComplex M [])),
      chainEuler (tensorObj (chainComplex s) (coefficientComplex M [])) h =
        ∑ᶠ p : (Ideal.ofList [] ⊔ Module.annihilator R M).minimalPrimes,
          twoListGenericEuler M [] p *
            chainEuler (coefficientComplex (ModuleCat.of R (R ⧸ p.1)) s)
              (fixedSupport_prime_finiteHomology s
                (Ideal.ofList [] ⊔ Module.annihilator R M) p.1 p.2.le) :=
  twoList_chainEuler_replacement M s [] hs

/-- Zero original coefficients give zero actual generic coefficients after
all first-stage homology and localization operations. -/
theorem zeroGenericCoefficient (M : ModuleCat R) [Module.Finite R M] [Subsingleton M]
    (t : List R) (p : (Ideal.ofList t ⊔ Module.annihilator R M).minimalPrimes) :
    twoListGenericEuler M t p = 0 := by
  have hzero : CategoryTheory.Limits.IsZero (coefficientComplex M t) :=
    Functor.map_isZero (coefficientFunctor t) (ModuleCat.isZero_of_subsingleton M)
  have hhom (n : ℕ) : Subsingleton ((coefficientComplex M t).homology n) :=
    ModuleCat.subsingleton_of_isZero
      (Functor.map_isZero (homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n) hzero)
  unfold twoListGenericEuler
  apply Finset.sum_eq_zero
  intro n _
  have := hhom n
  simp [fixedSupportGenericLength, integerLength]

end MotivicTest.KoszulTwoListReplacement
