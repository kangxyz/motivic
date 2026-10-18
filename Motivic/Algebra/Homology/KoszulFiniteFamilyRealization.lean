/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulCycleReplacement
public import Motivic.Algebra.Homology.KoszulExteriorCoefficientComparison
public import Motivic.Algebra.Homology.LengthEulerFiniteAlgebra

/-!
# Fixed-support realization for bounded finite-algebra coefficient families

Every coefficient retains restriction along the specified finite algebra map.
A single ideal annihilates every restricted coefficient, and its cut by the
last equation list is Artinian. These hypotheses prove finite length of the
final Koszul homology, before any integer conversion. Intermediate coefficient
modules need not have finite length.

The signed family Euler characteristic is both its fixed-minimal-prime
expansion and the sum over all maximal branches of the whole finite algebra,
weighted by the actual residue degrees. Localization is applied to the
finite-length whole homology; no branch ring is asserted finite over the base.
This is an Euler test identity, not an unrestricted map from coherent K-theory
to all-dimensional cycles. Geometric scalar attachments remain separate.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Motivic.LengthEuler

namespace Motivic.Koszul

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- The original coefficient module with its literal base-ring action. -/
abbrev finiteFamilyRestriction (M : ModuleCat B) : ModuleCat R :=
  (ModuleCat.restrictScalars (algebraMap R B)).obj M

set_option backward.isDefEq.respectTransparency false in
/-- Finiteness follows by restriction along the given finite algebra map. -/
instance finiteFamilyRestriction_finite [Module.Finite R B]
    (M : ModuleCat B) [Module.Finite B M] :
    Module.Finite R (finiteFamilyRestriction R B M) := by
  let := Module.compHom M (algebraMap R B)
  have : IsScalarTower R B M := IsScalarTower.of_compHom R B M
  change Module.Finite R M
  exact Module.Finite.trans B M

/-- The actual coefficient module localized at a maximal branch. -/
abbrev finiteFamilyLocalization (M : ModuleCat B) (q : MaximalSpectrum B) :
    ModuleCat (Localization.AtPrime q.asIdeal) :=
  (ModuleCat.extendScalars (algebraMap B (Localization.AtPrime q.asIdeal))).obj M

/-- The last equations act through the original algebra map and localization. -/
abbrev finiteFamilyLocalComplex (M : ModuleCat B) (s : List R)
    (q : MaximalSpectrum B) :=
  coefficientComplex (finiteFamilyLocalization B M q)
    ((s.map (algebraMap R B)).map (algebraMap B (Localization.AtPrime q.asIdeal)))

variable [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R B]

variable (M : ModuleCat B) [Module.Finite B M]
  (s : List R) (J : Ideal R)
  [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ J))]
  (hJ : J ≤ Module.annihilator R (finiteFamilyRestriction R B M))

include hJ in
omit [IsLocalRing R] in
/-- The final base-ring Koszul homology has finite length and finite support,
derived from the common support cut, without regularity on the coefficient. -/
theorem finiteFamilyRestriction_finiteHomology :
    FiniteHomology (coefficientComplex (finiteFamilyRestriction R B M) s) :=
  finiteHomology_of_artinian_quotient_of_le_annihilator _ s J hJ

include hJ in
omit [IsLocalRing R] in
set_option backward.isDefEq.respectTransparency false in
/-- Whole-algebra homology is finite because its literal scalar restriction
is the already finite base-ring Koszul homology. -/
theorem finiteFamilyWhole_finiteHomology :
    FiniteHomology (coefficientComplex M (s.map (algebraMap R B))) where
  finite_length n := by
    let H := (coefficientComplex M (s.map (algebraMap R B))).homology n
    let := Module.compHom H (algebraMap R B)
    have : IsScalarTower R B H := IsScalarTower.of_compHom R B H
    have hR := (finiteFamilyRestriction_finiteHomology R B M s J hJ).finite_length n
    rw [(coefficientRestrictHomologyIso (algebraMap R B) M s n).toLinearEquiv.length_eq] at hR
    change Module.length R H ≠ ⊤ at hR
    obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp
      (Module.length_ne_top_iff.mp hR)
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr
        ⟨isNoetherian_of_tower R hN, isArtinian_of_tower R hA⟩)
  finite_support := (Finset.range ((s.map (algebraMap R B)).length + 1)).finite_toSet.subset
    (coefficient_homology_length_support_subset M (s.map (algebraMap R B)))

include hJ in
omit [IsLocalRing R] in
/-- Every actual maximal-branch Koszul homology is finite. The proof localizes
the finite-length whole homology, rather than assuming the branch algebra finite. -/
theorem finiteFamilyLocal_finiteHomology (q : MaximalSpectrum B) :
    FiniteHomology (finiteFamilyLocalComplex R B M s q) :=
  ((finiteFamilyWhole_finiteHomology R B M s J hJ).finiteAlgebra_localized R B
    (coefficientComplex M (s.map (algebraMap R B))) q).of_quasiIso
      (coefficientExtendIso (algebraMap B (Localization.AtPrime q.asIdeal)) M
        (s.map (algebraMap R B))).hom

/-- Degreewise finite projection uses the whole finite algebra and every
maximal branch, with the canonical residue-field degrees of its actual map. -/
theorem finiteFamily_coefficient_projection :
    chainEuler (coefficientComplex (finiteFamilyRestriction R B M) s)
        (finiteFamilyRestriction_finiteHomology R B M s J hJ) =
      ∑ᶠ q : MaximalSpectrum B, (Module.finiteAlgebraResidueDegree R B q : ℤ) *
        chainEuler (finiteFamilyLocalComplex R B M s q)
          (finiteFamilyLocal_finiteHomology R B M s J hJ q) := by
  let : Finite (MaximalSpectrum B) := Module.finiteAlgebra_maximalSpectrum_finite R B
  let : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let K := coefficientComplex M (s.map (algebraMap R B))
  have hK := finiteFamilyWhole_finiteHomology R B M s J hJ
  calc
    _ = chainEuler (finiteAlgebraRestrictedComplex R B K)
        (hK.finiteAlgebra_restrict R B K) :=
      homologyEuler_eq_of_quasiIso (coefficientRestrictIso (algebraMap R B) M s).hom _ _ _
    _ = ∑ q : MaximalSpectrum B, (Module.finiteAlgebraResidueDegree R B q : ℤ) *
        chainEuler (finiteAlgebraLocalizedComplex B K q)
          (hK.finiteAlgebra_localized R B K q) :=
      chainEuler_finiteAlgebra R B K hK
    _ = _ := by
      rw [finsum_eq_sum_of_fintype]
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      exact homologyEuler_eq_of_quasiIso
        (coefficientExtendIso (algebraMap B (Localization.AtPrime q.asIdeal)) M
          (s.map (algebraMap R B))).hom _ _ _

end Motivic.Koszul

namespace Motivic.Koszul

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R B]
  (M : ℕ → ModuleCat B) [∀ n, Module.Finite B (M n)]
  (s : List R) (J : Ideal R)
  [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ J))]
  (hJ : ∀ n, J ≤ Module.annihilator R (finiteFamilyRestriction R B (M n)))

/-- The signed multiplicity of a finite set of degrees at a fixed support
prime. Each summand is an actual finite localized length. -/
def finiteFamilyGenericEuler (t : Finset ℕ) (sign : ℕ → ℤ)
    (p : J.minimalPrimes) : ℤ :=
  ∑ n ∈ t, sign n * fixedSupportGenericLength
    (finiteFamilyRestriction R B (M n)) J (hJ n) p

/-- Fixed-support replacement for any finite signed family. There is one
minimal-prime set for every degree; no purity assumption enters. -/
theorem finiteFamily_chainEuler_replacement (t : Finset ℕ) (sign : ℕ → ℤ)
    (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R) :
    (∑ n ∈ t, sign n *
      chainEuler (coefficientComplex (finiteFamilyRestriction R B (M n)) s)
        (finiteFamilyRestriction_finiteHomology R B (M n) s J (hJ n))) =
      ∑ᶠ p : J.minimalPrimes, finiteFamilyGenericEuler R B M J hJ t sign p *
        chainEuler (coefficientComplex (ModuleCat.of R (R ⧸ p.1)) s)
          (fixedSupport_prime_finiteHomology s J p.1 p.2.le) := by
  classical
  let : Fintype J.minimalPrimes :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing R J).fintype
  have hLayer (n : ℕ) :
      chainEuler (coefficientComplex (finiteFamilyRestriction R B (M n)) s)
          (finiteFamilyRestriction_finiteHomology R B (M n) s J (hJ n)) =
        ∑ᶠ p : J.minimalPrimes,
          fixedSupportGenericLength (finiteFamilyRestriction R B (M n)) J (hJ n) p *
            chainEuler (coefficientComplex (ModuleCat.of R (R ⧸ p.1)) s)
              (fixedSupport_prime_finiteHomology s J p.1 p.2.le) :=
    fixedSupport_chainEuler_replacement _ s J hs (hJ n)
  simp_rw [hLayer, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [finiteFamilyGenericEuler, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  exact (mul_assoc _ _ _).symm

/-- All maximal branches and all chosen degrees commute as genuinely finite
sums. The residue weight is the one attached to the original finite algebra. -/
theorem finiteFamily_chainEuler_projection (t : Finset ℕ) (sign : ℕ → ℤ) :
    (∑ n ∈ t, sign n *
      chainEuler (coefficientComplex (finiteFamilyRestriction R B (M n)) s)
        (finiteFamilyRestriction_finiteHomology R B (M n) s J (hJ n))) =
      ∑ᶠ q : MaximalSpectrum B, (Module.finiteAlgebraResidueDegree R B q : ℤ) *
        ∑ n ∈ t, sign n * chainEuler (finiteFamilyLocalComplex R B (M n) s q)
          (finiteFamilyLocal_finiteHomology R B (M n) s J (hJ n) q) := by
  classical
  let : Finite (MaximalSpectrum B) := Module.finiteAlgebra_maximalSpectrum_finite R B
  let : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  have hLayer (n : ℕ) := finiteFamily_coefficient_projection R B (M n) s J (hJ n)
  simp_rw [hLayer, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro n _
  exact mul_left_comm _ _ _

/-- The common fixed-support cycle test equals the entire finite-fiber test. -/
theorem finiteFamily_cycle_realization (t : Finset ℕ) (sign : ℕ → ℤ)
    (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R) :
    (∑ᶠ p : J.minimalPrimes, finiteFamilyGenericEuler R B M J hJ t sign p *
      chainEuler (coefficientComplex (ModuleCat.of R (R ⧸ p.1)) s)
        (fixedSupport_prime_finiteHomology s J p.1 p.2.le)) =
      ∑ᶠ q : MaximalSpectrum B, (Module.finiteAlgebraResidueDegree R B q : ℤ) *
        ∑ n ∈ t, sign n * chainEuler (finiteFamilyLocalComplex R B (M n) s q)
          (finiteFamilyLocal_finiteHomology R B (M n) s J (hJ n) q) :=
  (finiteFamily_chainEuler_replacement R B M s J hJ t sign hs).symm.trans
    (finiteFamily_chainEuler_projection R B M s J hJ t sign)

omit [IsLocalRing R] in
/-- A common bound on the original coefficients bounds the genuine family
Euler summand, including after restriction of scalars. -/
theorem boundedFamily_chainEuler_support (N : ℕ)
    (hzero : ∀ n, N < n → IsZero (M n)) :
    Function.support (fun n => (-1 : ℤ) ^ n *
      chainEuler (coefficientComplex (finiteFamilyRestriction R B (M n)) s)
        (finiteFamilyRestriction_finiteHomology R B (M n) s J (hJ n))) ⊆
      (Finset.range (N + 1) : Set ℕ) := by
  intro n hn
  by_contra hnot
  have hbound : N < n := by simpa using hnot
  have : Subsingleton (finiteFamilyRestriction R B (M n)) :=
    ModuleCat.subsingleton_of_isZero
      (Functor.map_isZero (ModuleCat.restrictScalars (algebraMap R B)) (hzero n hbound))
  exact hn ((congrArg (fun z : ℤ => (-1 : ℤ) ^ n * z)
    (koszulDimension_chainEuler_zero_of_subsingleton
      (finiteFamilyRestriction R B (M n)) s
      (finiteFamilyRestriction_finiteHomology R B (M n) s J (hJ n)))).trans
    (mul_zero _))

omit [IsLocalRing R] in
/-- The very same coefficient bound controls every maximal branch. -/
theorem boundedFamily_local_chainEuler_support (N : ℕ)
    (hzero : ∀ n, N < n → IsZero (M n)) (q : MaximalSpectrum B) :
    Function.support (fun n => (-1 : ℤ) ^ n *
      chainEuler (finiteFamilyLocalComplex R B (M n) s q)
        (finiteFamilyLocal_finiteHomology R B (M n) s J (hJ n) q)) ⊆
      (Finset.range (N + 1) : Set ℕ) := by
  intro n hn
  by_contra hnot
  have hbound : N < n := by simpa using hnot
  have : Subsingleton (finiteFamilyLocalization B (M n) q) :=
    ModuleCat.subsingleton_of_isZero
      (Functor.map_isZero
        (ModuleCat.extendScalars (algebraMap B (Localization.AtPrime q.asIdeal)))
        (hzero n hbound))
  exact hn ((congrArg (fun z : ℤ => (-1 : ℤ) ^ n * z)
    (koszulDimension_chainEuler_zero_of_subsingleton
      (finiteFamilyLocalization B (M n) q)
      ((s.map (algebraMap R B)).map (algebraMap B (Localization.AtPrime q.asIdeal)))
      (finiteFamilyLocal_finiteHomology R B (M n) s J (hJ n) q))).trans
    (mul_zero _))

omit [IsLocalRing R] in
/-- The common coefficient bound also bounds the actual localized generic
lengths. In particular their all-degree sum has genuinely finite support. -/
theorem boundedFamily_generic_support (N : ℕ)
    (hzero : ∀ n, N < n → IsZero (M n)) (p : J.minimalPrimes) :
    Function.support (fun n => (-1 : ℤ) ^ n * fixedSupportGenericLength
      (finiteFamilyRestriction R B (M n)) J (hJ n) p) ⊆
      (Finset.range (N + 1) : Set ℕ) := by
  intro n hn
  by_contra hnot
  have hbound : N < n := by simpa using hnot
  have : Subsingleton (finiteFamilyRestriction R B (M n)) :=
    ModuleCat.subsingleton_of_isZero
      (Functor.map_isZero (ModuleCat.restrictScalars (algebraMap R B)) (hzero n hbound))
  exact hn (by simp [fixedSupportGenericLength, integerLength])

omit [IsLocalRing R] in
/-- The bounded generic coefficient is the actual all-degree alternating
localized length, independently of the choice of a valid common bound. -/
theorem boundedFamilyGenericEuler_eq_finsum (N : ℕ)
    (hzero : ∀ n, N < n → IsZero (M n)) (p : J.minimalPrimes) :
    finiteFamilyGenericEuler R B M J hJ (Finset.range (N + 1)) (fun n => (-1) ^ n) p =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * fixedSupportGenericLength
        (finiteFamilyRestriction R B (M n)) J (hJ n) p :=
  (finsum_eq_sum_of_support_subset _
    (boundedFamily_generic_support R B M J hJ N hzero p)).symm

/-- The all-degree signed family Euler characteristic is its fixed-support
minimal-prime expansion. The finite range is derived from the supplied common
zero bound; no infinite-support default value is used. -/
theorem boundedFamily_chainEuler_replacement (N : ℕ)
    (hzero : ∀ n, N < n → IsZero (M n))
    (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      chainEuler (coefficientComplex (finiteFamilyRestriction R B (M n)) s)
        (finiteFamilyRestriction_finiteHomology R B (M n) s J (hJ n))) =
      ∑ᶠ p : J.minimalPrimes,
        finiteFamilyGenericEuler R B M J hJ (Finset.range (N + 1)) (fun n => (-1) ^ n) p *
          chainEuler (coefficientComplex (ModuleCat.of R (R ⧸ p.1)) s)
            (fixedSupport_prime_finiteHomology s J p.1 p.2.le) := by
  rw [finsum_eq_sum_of_support_subset _
    (boundedFamily_chainEuler_support R B M s J hJ N hzero)]
  exact finiteFamily_chainEuler_replacement R B M s J hJ _ _ hs

/-- The all-degree finite-family Euler characteristic is the residue-weighted
sum of all-degree Euler characteristics on every maximal branch. -/
theorem boundedFamily_chainEuler_projection (N : ℕ)
    (hzero : ∀ n, N < n → IsZero (M n)) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      chainEuler (coefficientComplex (finiteFamilyRestriction R B (M n)) s)
        (finiteFamilyRestriction_finiteHomology R B (M n) s J (hJ n))) =
      ∑ᶠ q : MaximalSpectrum B, (Module.finiteAlgebraResidueDegree R B q : ℤ) *
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * chainEuler (finiteFamilyLocalComplex R B (M n) s q)
          (finiteFamilyLocal_finiteHomology R B (M n) s J (hJ n) q) := by
  rw [finsum_eq_sum_of_support_subset _
    (boundedFamily_chainEuler_support R B M s J hJ N hzero),
    finiteFamily_chainEuler_projection R B M s J hJ]
  apply finsum_congr
  intro q
  congr 1
  exact (finsum_eq_sum_of_support_subset _
    (boundedFamily_local_chainEuler_support R B M s J hJ N hzero q)).symm

/-- The bounded-family realization engine: fixed-support generic multiplicities
and the actual all-branch finite pushforward give the same final Koszul test. -/
theorem boundedFamily_cycle_realization (N : ℕ)
    (hzero : ∀ n, N < n → IsZero (M n))
    (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R) :
    (∑ᶠ p : J.minimalPrimes,
      finiteFamilyGenericEuler R B M J hJ (Finset.range (N + 1)) (fun n => (-1) ^ n) p *
        chainEuler (coefficientComplex (ModuleCat.of R (R ⧸ p.1)) s)
          (fixedSupport_prime_finiteHomology s J p.1 p.2.le)) =
      ∑ᶠ q : MaximalSpectrum B, (Module.finiteAlgebraResidueDegree R B q : ℤ) *
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * chainEuler (finiteFamilyLocalComplex R B (M n) s q)
          (finiteFamilyLocal_finiteHomology R B (M n) s J (hJ n) q) :=
  (boundedFamily_chainEuler_replacement R B M s J hJ N hzero hs).symm.trans
    (boundedFamily_chainEuler_projection R B M s J hJ N hzero)

/-- The common realization formula with all three degree sums written over
all natural numbers. Every such sum has the same proved finite degree bound. -/
theorem boundedFamily_cycle_realization_finsum (N : ℕ)
    (hzero : ∀ n, N < n → IsZero (M n))
    (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R) :
    (∑ᶠ p : J.minimalPrimes,
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * fixedSupportGenericLength
        (finiteFamilyRestriction R B (M n)) J (hJ n) p) *
        chainEuler (coefficientComplex (ModuleCat.of R (R ⧸ p.1)) s)
          (fixedSupport_prime_finiteHomology s J p.1 p.2.le)) =
      ∑ᶠ q : MaximalSpectrum B, (Module.finiteAlgebraResidueDegree R B q : ℤ) *
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * chainEuler (finiteFamilyLocalComplex R B (M n) s q)
          (finiteFamilyLocal_finiteHomology R B (M n) s J (hJ n) q) := by
  simpa only [boundedFamilyGenericEuler_eq_finsum R B M J hJ N hzero] using
    boundedFamily_cycle_realization R B M s J hJ N hzero hs

end Motivic.Koszul
