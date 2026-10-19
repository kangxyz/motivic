/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.Coefficient.EulerAdditivity
public import Motivic.Aglib.Algebra.Homology.Koszul.DimensionZeroHead
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
# Actual Koszul Euler length along a prime filtration

The genuine coefficient functor carries the successive quotient equivalences
and short exact sequences of an actual prime filtration to Koszul complexes.
Their all-degree Euler characteristics telescope. A common fixed support
ideal supplies finite homology of every term and every factor.
-/

@[expose] public section

universe u

open CategoryTheory _root_.HomologicalComplex.ModuleLengthEuler Module

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- The actual coefficient functor transports a coefficient linear equivalence
and therefore preserves all-degree finite-homology Euler length. -/
theorem coefficient_chainEuler_eq_of_linearEquiv
    (M N : ModuleCat R) (e : M ≃ₗ[R] N) (s : List R)
    (hM : FiniteHomology (coefficientComplex M s))
    (hN : FiniteHomology (coefficientComplex N s)) :
    chainEuler (coefficientComplex M s) hM = chainEuler (coefficientComplex N s) hN :=
  homologyEuler_eq_of_quasiIso ((coefficientFunctor s).mapIso e.toModuleIso).hom _ hM hN

/-- Every quotient ideal containing the fixed support ideal has finite Koszul
homology under the common Artinian equation-support hypothesis. -/
theorem fixedSupport_prime_finiteHomology (s : List R) (J p : Ideal R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ J))] (hp : J ≤ p) :
    FiniteHomology (coefficientComplex (ModuleCat.of R (R ⧸ p)) s) :=
  finiteHomology_of_artinian_quotient_of_le_annihilator _ s J
    (by simpa only [Ideal.annihilator_quotient] using hp)

/-- The genuine Koszul Euler coefficient on a quotient containing the fixed
support. The zero extension outside that support only makes a total function
for finite list summation; every used filtration or minimal prime is inside. -/
noncomputable def fixedSupportPrimeEuler (s : List R) (J : Ideal R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ J))] (p : Ideal R) : ℤ := by
  classical
  exact if hp : J ≤ p then chainEuler (coefficientComplex (ModuleCat.of R (R ⧸ p)) s)
    (fixedSupport_prime_finiteHomology s J p hp) else 0

/-- On the fixed support this is the actual chain Euler characteristic. -/
theorem fixedSupportPrimeEuler_eq (s : List R) (J p : Ideal R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ J))] (hp : J ≤ p)
    (h : FiniteHomology (coefficientComplex (ModuleCat.of R (R ⧸ p)) s)) :
    fixedSupportPrimeEuler s J p =
      chainEuler (coefficientComplex (ModuleCat.of R (R ⧸ p)) s) h := by
  classical
  simp only [fixedSupportPrimeEuler, dite_eq_left hp]

/-- Telescoping along literal successive quotient isomorphisms computes the
actual coefficient-complex Euler characteristic. -/
theorem primeFiltration_chainEuler_eq_add_sum (M : ModuleCat R) [Module.Finite R M]
    {U : Submodule R M} (D : Module.PrimeFiltrationFrom M U) (s : List R) (J : Ideal R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ J))] (hJ : J ≤ Module.annihilator R M)
    (hM : FiniteHomology (coefficientComplex M s))
    (hU : FiniteHomology (coefficientComplex (ModuleCat.of R U) s)) :
    chainEuler (coefficientComplex M s) hM =
      chainEuler (coefficientComplex (ModuleCat.of R U) s) hU +
        (D.primes.map (fixedSupportPrimeEuler s J)).sum := by
  induction D with
  | top =>
    simp only [Module.PrimeFiltrationFrom.primes, List.map_nil, List.sum_nil, add_zero]
    exact coefficient_chainEuler_eq_of_linearEquiv M _ (Submodule.topEquiv.symm) s _ _
  | @step U V hUV p hp e tail ih =>
    have hJV : J ≤ Module.annihilator R V :=
      hJ.trans (V.subtype.annihilator_le_of_injective V.injective_subtype)
    have hV := finiteHomology_of_artinian_quotient_of_le_annihilator (ModuleCat.of R V) s J hJV
    let C : Submodule R V := U.comap V.subtype
    let f : U →ₗ[R] V := Submodule.inclusion hUV.le
    have hex : Function.Exact f C.mkQ := by
      apply LinearMap.exact_iff.mpr
      simp only [f, C, Submodule.range_inclusion, Submodule.ker_mkQ]
    have hJC : J ≤ Module.annihilator R (V ⧸ C) :=
      hJV.trans (C.mkQ.annihilator_le_of_surjective C.mkQ_surjective)
    have hC := finiteHomology_of_artinian_quotient_of_le_annihilator
      (ModuleCat.of R (V ⧸ C)) s J hJC
    have hJp : J ≤ p := by
      change J ≤ Module.annihilator R (V ⧸ U.comap V.subtype) at hJC
      rwa [e.annihilator_eq, Ideal.annihilator_quotient] at hJC
    have hP := fixedSupport_prime_finiteHomology s J p hJp
    let S := ModuleCat.shortComplexOfCompEqZero f C.mkQ hex.linearMap_comp_eq_zero
    have hS : S.ShortExact := ModuleCat.shortComplex_shortExact _ hex
      (Submodule.inclusion_injective hUV.le) C.mkQ_surjective
    have hadd := coefficient_chainEuler_add_of_shortExact s S hS hU hV hC
    have he := coefficient_chainEuler_eq_of_linearEquiv (ModuleCat.of R (V ⧸ C))
      (ModuleCat.of R (R ⧸ p)) e s hC hP
    rw [← fixedSupportPrimeEuler_eq s J p hJp hP] at he
    have hi := ih hV
    rw [hadd, he] at hi
    simpa only [Module.PrimeFiltrationFrom.primes, List.map_cons, List.sum_cons, add_assoc] using hi

/-- The initial zero submodule contributes zero to the actual telescope. -/
theorem primeFiltration_chainEuler_eq_sum (M : ModuleCat R) [Module.Finite R M]
    (D : Module.PrimeFiltrationFrom M ⊥) (s : List R) (J : Ideal R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ J))] (hJ : J ≤ Module.annihilator R M)
    (hM : FiniteHomology (coefficientComplex M s)) :
    chainEuler (coefficientComplex M s) hM =
      (D.primes.map (fixedSupportPrimeEuler s J)).sum := by
  have hbot := finiteHomology_of_artinian_quotient_of_le_annihilator
    (ModuleCat.of R (⊥ : Submodule R M)) s J
    (hJ.trans ((⊥ : Submodule R M).subtype.annihilator_le_of_injective
      (Submodule.injective_subtype _)))
  have he := primeFiltration_chainEuler_eq_add_sum M D s J hJ hM hbot
  rw [koszulDimension_chainEuler_zero_of_subsingleton
    (ModuleCat.of R (⊥ : Submodule R M)) s hbot, zero_add] at he
  exact he

end ChainComplex.Koszul
