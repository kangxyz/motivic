/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.ClosedImmersionGenericCycleCoefficient

/-!
# A fixed-list Euler test for closed fundamental cycles

A closed immersion contributes its literal kernel quotient over the original
ambient stalk. An Artinian cut by one fixed list permits replacement by ambient
component generics, with coefficients in the pushed full fundamental cycle.
The list and scalars remain identical in every term, including for nonreduced
or lower-dimensional closed supports. No purity or flatness is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Motivic Motivic.LengthEuler

universe u v

namespace AlgebraicGeometry

/-- Minimal primes in the actual stalk correspond to ambient component generics
specializing to its point. -/
def stalkMinimalPrimeGenericEquiv (P : Scheme.{u}) (x : P) :
    minimalPrimes (P.presheaf.stalk x) ≃ {q : genericPoints P // q.1 ⤳ x} :=
  (specGenericMinimalPrimeEquiv _).symm.trans (stalkGenericPointEquiv P x)

/-- The inverse index retains the literal prime in the original stalk. -/
theorem stalkMinimalPrimeGenericEquiv_symm_val (P : Scheme.{u}) (x : P)
    (q : {q : genericPoints P // q.1 ⤳ x}) :
    ((stalkMinimalPrimeGenericEquiv P x).symm q).1 =
      (genericStalkLocalizationPrime P x q).asIdeal := rfl

/-- Local Noetherianity suffices for finiteness of the ambient component generics
specializing to a fixed point; global quasi-compactness is unnecessary. -/
theorem finite_genericPoints_specializing (P : Scheme.{u}) [IsLocallyNoetherian P]
    (x : P) : Finite {q : genericPoints P // q.1 ⤳ x} := by
  let : Fintype (minimalPrimes (P.presheaf.stalk x)) :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing (P.presheaf.stalk x) ⊥).fintype
  exact Finite.of_equiv _ (stalkMinimalPrimeGenericEquiv P x)

/-- The closed-support Koszul Euler characteristic is the Euler test of the
actual pushed fundamental cycle. All terms use the same original stalk and list.
Nongeneric filtration primes vanish by the Artinian cut and dimension drop. -/
theorem closedImmersion_chainEuler_replacement {E P : Scheme.{u}}
    (j : E ⟶ P) [IsClosedImmersion j] [IsNoetherian E] [IsLocallyNoetherian P]
    (x : P) (s : List (P.presheaf.stalk x))
    [IsArtinianRing ((P.presheaf.stalk x) ⧸ (Ideal.ofList s ⊔ ⊥))]
    (hs : ∀ r ∈ s, r ∈ IsLocalRing.maximalIdeal (P.presheaf.stalk x)) :
    chainEuler (Koszul.coefficientComplex
        (ModuleCat.of (P.presheaf.stalk x) ((P.presheaf.stalk x) ⧸ j.ker.stalk x)) s)
        (Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ s ⊥ bot_le) =
      ∑ᶠ q : {q : genericPoints P // q.1 ⤳ x},
        IntegralCycle.toPoints (IntegralCycle.finitePushforward j (fundamentalCycle E)) q.1.1 *
          chainEuler (Koszul.coefficientComplex
            (ModuleCat.of (P.presheaf.stalk x)
              ((P.presheaf.stalk x) ⧸ (genericStalkLocalizationPrime P x q).asIdeal)) s)
            (Koszul.fixedSupport_prime_finiteHomology s ⊥
              (genericStalkLocalizationPrime P x q).asIdeal bot_le) := by
  refine (Koszul.fixedSupport_chainEuler_replacement _ s ⊥ hs bot_le).trans ?_
  rw [← finsum_comp_equiv (stalkMinimalPrimeGenericEquiv P x).symm]
  apply finsum_congr
  intro q
  have hq : (stalkMinimalPrimeGenericEquiv P x).symm q =
      ⟨(genericStalkLocalizationPrime P x q).asIdeal,
        genericStalkLocalizationPrime_mem_minimalPrimes P x q⟩ := rfl
  rw [hq, fixedSupportGenericLength_closedImmersion]

/-- A finite signed equality of actual pushed closed fundamental cycles gives
an equality of their fixed-list Euler tests, with no geometric purity assumption. -/
theorem closedImmersion_chainEuler_eq_sum_of_fundamentalCycle_eq
    {E₀ P : Scheme.{u}} [IsNoetherian E₀] [IsLocallyNoetherian P]
    (j₀ : E₀ ⟶ P) [IsClosedImmersion j₀]
    {ι : Type v} [Fintype ι] (E : ι → Scheme.{u}) [∀ i, IsNoetherian (E i)]
    (j : ∀ i, E i ⟶ P) [∀ i, IsClosedImmersion (j i)] (c : ι → ℤ)
    (hcycle : IntegralCycle.finitePushforward j₀ (fundamentalCycle E₀) =
      ∑ i, c i • IntegralCycle.finitePushforward (j i) (fundamentalCycle (E i)))
    (x : P) (s : List (P.presheaf.stalk x))
    [IsArtinianRing ((P.presheaf.stalk x) ⧸ (Ideal.ofList s ⊔ ⊥))]
    (hs : ∀ r ∈ s, r ∈ IsLocalRing.maximalIdeal (P.presheaf.stalk x)) :
    chainEuler (Koszul.coefficientComplex
        (ModuleCat.of (P.presheaf.stalk x) ((P.presheaf.stalk x) ⧸ j₀.ker.stalk x)) s)
        (Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ s ⊥ bot_le) =
      ∑ i, c i * chainEuler (Koszul.coefficientComplex
        (ModuleCat.of (P.presheaf.stalk x) ((P.presheaf.stalk x) ⧸ (j i).ker.stalk x)) s)
        (Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ s ⊥ bot_le) := by
  classical
  let := finite_genericPoints_specializing P x
  let := Fintype.ofFinite {q : genericPoints P // q.1 ⤳ x}
  simp_rw [closedImmersion_chainEuler_replacement _ x s hs, finsum_eq_sum_of_fintype]
  simp only [hcycle, map_sum, map_zsmul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    zsmul_eq_mul, Int.cast_id, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- For the identity closed immersion, the quotient by its zero kernel has the
same actual Koszul Euler characteristic as the regular ambient stalk module. -/
theorem id_closedImmersion_chainEuler_eq (P : Scheme.{u}) [IsLocallyNoetherian P]
    (x : P) (s : List (P.presheaf.stalk x))
    [IsArtinianRing ((P.presheaf.stalk x) ⧸ (Ideal.ofList s ⊔ ⊥))] :
    chainEuler (Koszul.coefficientComplex
        (ModuleCat.of (P.presheaf.stalk x)
          ((P.presheaf.stalk x) ⧸ (𝟙 P : P ⟶ P).ker.stalk x)) s)
        (Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ s ⊥ bot_le) =
      chainEuler (Koszul.coefficientComplex
        (ModuleCat.of (P.presheaf.stalk x) (P.presheaf.stalk x)) s)
        (Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ s ⊥ bot_le) := by
  apply Koszul.coefficient_chainEuler_eq_of_linearEquiv
  have hker : (𝟙 P : P ⟶ P).ker.stalk x = ⊥ := by simp
  exact (Ideal.quotientEquivAlgOfEq (P.presheaf.stalk x) hker).toLinearEquiv.trans
    (AlgEquiv.quotientBot (P.presheaf.stalk x) (P.presheaf.stalk x)).toLinearEquiv

/-- The regular ambient stalk module satisfies the finite signed fundamental-
cycle formula, using the identical list on every actual closed-support quotient. -/
theorem chainEuler_eq_sum_of_fundamentalCycle_eq
    {P : Scheme.{u}} [IsNoetherian P]
    {ι : Type v} [Fintype ι] (E : ι → Scheme.{u}) [∀ i, IsNoetherian (E i)]
    (j : ∀ i, E i ⟶ P) [∀ i, IsClosedImmersion (j i)] (c : ι → ℤ)
    (hcycle : fundamentalCycle P =
      ∑ i, c i • IntegralCycle.finitePushforward (j i) (fundamentalCycle (E i)))
    (x : P) (s : List (P.presheaf.stalk x))
    [IsArtinianRing ((P.presheaf.stalk x) ⧸ (Ideal.ofList s ⊔ ⊥))]
    (hs : ∀ r ∈ s, r ∈ IsLocalRing.maximalIdeal (P.presheaf.stalk x)) :
    chainEuler (Koszul.coefficientComplex
        (ModuleCat.of (P.presheaf.stalk x) (P.presheaf.stalk x)) s)
        (Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ s ⊥ bot_le) =
      ∑ i, c i * chainEuler (Koszul.coefficientComplex
        (ModuleCat.of (P.presheaf.stalk x) ((P.presheaf.stalk x) ⧸ (j i).ker.stalk x)) s)
        (Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ s ⊥ bot_le) := by
  rw [← id_closedImmersion_chainEuler_eq]
  exact closedImmersion_chainEuler_eq_sum_of_fundamentalCycle_eq (𝟙 P) E j c
    (by simpa only [IntegralCycle.finitePushforward_id, AddMonoidHom.id_apply] using hcycle)
    x s hs

end AlgebraicGeometry
