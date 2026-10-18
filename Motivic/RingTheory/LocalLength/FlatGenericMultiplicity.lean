/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.LocalLength.FixedSupportMultiplicity
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Actual generic multiplicities under flat base change

Flat going down identifies the contraction of a generic point of the fixed
base-changed support. Localized actual prime filtrations then compute the
base-changed generic length, retaining the closed-fiber multiplicity.
-/

@[expose] public section

open scoped TensorProduct
open TensorProduct

universe u v w

namespace Module

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Flat going down sends a minimal prime of an extended fixed support ideal
to a minimal prime of the original support ideal. -/
theorem flatGeneric_under_mem_minimalPrimes [Module.Flat A B]
    (I : Ideal A) (q : Ideal B) [q.IsPrime]
    (hq : q ∈ (I.map (algebraMap A B)).minimalPrimes) :
    q.under A ∈ I.minimalPrimes := by
  refine ⟨⟨inferInstance, Ideal.map_le_iff_le_comap.mp hq.le⟩, ?_⟩
  intro p hp hpq
  have : p.IsPrime := hp.1
  obtain ⟨P, hPq, hP, hPp⟩ := Ideal.exists_ideal_le_liesOver_of_le q hpq
  have : P.IsPrime := hP
  have : P.LiesOver p := hPp
  have hIP : I.map (algebraMap A B) ≤ P := by
    apply Ideal.map_le_iff_le_comap.mpr
    change I ≤ P.under A
    rw [← P.over_def p]
    exact hp.2
  have he : P = q := hPq.antisymm (hq.2 ⟨hP, hIP⟩ hPq)
  rw [P.over_def p, he]

/-- The actual localized base-change module is identified by cancellation of
the intermediate tensor factor, with its localization-ring scalar action. -/
noncomputable def flatGenericLocalizedBaseChangeEquiv
    (M : Type w) [AddCommGroup M] [Module A M] (q : Ideal B) [q.IsPrime] :
    Localization.AtPrime q ⊗[B] (B ⊗[A] M) ≃ₗ[Localization.AtPrime q]
      Localization.AtPrime q ⊗[A] M :=
  AlgebraTensorModule.cancelBaseChange A B (Localization.AtPrime q) (Localization.AtPrime q) M

/-- Prime-quotient factors not contained in the contraction vanish after
actual base change to the target local ring. -/
theorem flatGeneric_primeQuotient_length_zero (q : Ideal B) [q.IsPrime]
    (p : Ideal A) (hp : ¬ p ≤ q.under A) :
    Module.length (Localization.AtPrime q) (Localization.AtPrime q ⊗[A] (A ⧸ p)) = 0 := by
  obtain ⟨a, ha, haq⟩ := SetLike.not_le_iff_exists.mp hp
  have hunit : IsUnit (algebraMap A (Localization.AtPrime q) a) := by
    rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime q)]
    exact IsLocalization.map_units (Localization.AtPrime q)
      (⟨algebraMap A B a, haq⟩ : q.primeCompl)
  have htop : p.map (algebraMap A (Localization.AtPrime q)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ ha) hunit
  rw [← (Ideal.qoutMapEquivTensorQout (I := p) (Localization.AtPrime q)).length_eq, htop]
  exact Module.length_eq_zero

/-- Localizing the literal flat-base-changed filtration yields the generic
length formula before any conversion from extended natural numbers. The
closed-fiber factor is retained and is not assumed to equal one. -/
theorem flatGeneric_length_eq_mul [IsNoetherianRing A] [Module.Flat A B]
    (M : Type w) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : I ≤ Module.annihilator A M) (q : Ideal B) [q.IsPrime]
    (hq : q ∈ (I.map (algebraMap A B)).minimalPrimes) :
    Module.length (Localization.AtPrime q) (Localization.AtPrime q ⊗[A] M) =
      Module.length (Localization.AtPrime (q.under A))
        (Localization.AtPrime (q.under A) ⊗[A] M) *
      Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⊗[A] (A ⧸ q.under A)) := by
  classical
  obtain ⟨D⟩ := Module.nonempty_primeFiltration (A := A) M
  have hp := flatGeneric_under_mem_minimalPrimes I q hq
  rw [D.fixedSupport_localized_length_eq_count I hI (q.under A) hp]
  rw [D.length_baseChange_eq_add_sum (Localization.AtPrime q), Module.length_eq_zero, zero_add]
  have hfac (p : Ideal A) (hpD : p ∈ D.primes) :
      Module.length (Localization.AtPrime q) (Localization.AtPrime q ⊗[A] (A ⧸ p)) =
        if p = q.under A then Module.length (Localization.AtPrime q)
          (Localization.AtPrime q ⊗[A] (A ⧸ q.under A)) else 0 := by
    by_cases he : p = q.under A
    · subst p
      simp
    · rw [ite_eq_right he]
      apply flatGeneric_primeQuotient_length_zero q p
      intro hle
      apply he
      exact hle.antisymm (hp.2 ⟨D.primes_isPrime p hpD,
        hI.trans (Module.annihilator_le_of_mem_support (D.prime_mem_support p hpD))⟩ hle)
  rw [List.map_congr_left hfac]
  induction D.primes with
  | nil => simp
  | cons p ps ih =>
    by_cases he : p = q.under A
    · subst p
      simpa [add_mul, add_comm] using congrArg
        (fun x => x + Module.length (Localization.AtPrime q)
          (Localization.AtPrime q ⊗[A] (A ⧸ q.under A))) ih
    · simpa [he] using ih

/-- The same multiplicity law on the actual localization of the base-changed
module, through the scalar-compatible tensor cancellation equivalence. -/
theorem flatGeneric_localizedBaseChange_length [IsNoetherianRing A] [Module.Flat A B]
    (M : Type w) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : I ≤ Module.annihilator A M) (q : Ideal B) [q.IsPrime]
    (hq : q ∈ (I.map (algebraMap A B)).minimalPrimes) :
    Module.length (Localization.AtPrime q) (Localization.AtPrime q ⊗[B] (B ⊗[A] M)) =
      Module.length (Localization.AtPrime (q.under A))
        (Localization.AtPrime (q.under A) ⊗[A] M) *
      Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⊗[A] (A ⧸ q.under A)) := by
  rw [(flatGenericLocalizedBaseChangeEquiv M q).length_eq]
  exact flatGeneric_length_eq_mul M I hI q hq

/-- The localization of the source module can be extended through the actual
local ring map to recover direct target-local base change. -/
noncomputable def flatGenericSourceLocalizationEquiv
    (M : Type w) [AddCommGroup M] [Module A M] (q : Ideal B) [q.IsPrime] :
    letI := Localization.AtPrime.algebraOfLiesOver (q.under A) q
    Localization.AtPrime q ⊗[Localization.AtPrime (q.under A)]
      (Localization.AtPrime (q.under A) ⊗[A] M) ≃ₗ[Localization.AtPrime q]
        Localization.AtPrime q ⊗[A] M := by
  letI := Localization.AtPrime.algebraOfLiesOver (q.under A) q
  exact AlgebraTensorModule.cancelBaseChange A (Localization.AtPrime (q.under A))
    (Localization.AtPrime q) (Localization.AtPrime q) M

/-- The tensor prime-quotient factor is the literal closed fiber quotient,
with its actual target-local-ring module action. -/
noncomputable def flatGenericClosedFiberEquiv (q : Ideal B) [q.IsPrime] :
    (Localization.AtPrime q ⧸ (q.under A).map (algebraMap A (Localization.AtPrime q)))
      ≃ₗ[Localization.AtPrime q] Localization.AtPrime q ⊗[A] (A ⧸ q.under A) :=
  Ideal.qoutMapEquivTensorQout (I := q.under A) (Localization.AtPrime q)

/-- An extended annihilating support ideal kills the actual base-changed
module, proved on pure tensors and then on all tensor elements. -/
theorem flatGeneric_map_le_annihilator (M : Type w) [AddCommGroup M] [Module A M]
    (I : Ideal A) (hI : I ≤ Module.annihilator A M) :
    I.map (algebraMap A B) ≤ Module.annihilator B (B ⊗[A] M) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  change algebraMap A B a ∈ Module.annihilator B (B ⊗[A] M)
  apply Module.mem_annihilator.mpr
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
    rw [IsScalarTower.algebraMap_smul, ← TensorProduct.tmul_smul,
      Module.mem_annihilator.mp (hI ha) m, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

/-- At a generic point of the fixed target support, the actual localized
base-changed module has finite length. This finiteness does not need flatness. -/
theorem flatGeneric_target_length_ne_top [IsNoetherianRing B]
    (M : Type w) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : I ≤ Module.annihilator A M) (q : Ideal B) [q.IsPrime]
    (hq : q ∈ (I.map (algebraMap A B)).minimalPrimes) :
    Module.length (Localization.AtPrime q) (Localization.AtPrime q ⊗[A] M) ≠ ⊤ := by
  have he := fixedSupport_localized_length_ne_top (B ⊗[A] M) (I.map (algebraMap A B))
    (flatGeneric_map_le_annihilator M I hI) q hq
  rwa [(flatGenericLocalizedBaseChangeEquiv M q).length_eq] at he

/-- All three lengths in the generic multiplicity formula are finite. The
closed fiber is retained as a genuine possibly nonreduced quotient. -/
theorem flatGeneric_lengths_ne_top [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Flat A B] (M : Type w) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : I ≤ Module.annihilator A M) (q : Ideal B) [q.IsPrime]
    (hq : q ∈ (I.map (algebraMap A B)).minimalPrimes) :
    Module.length (Localization.AtPrime (q.under A))
        (Localization.AtPrime (q.under A) ⊗[A] M) ≠ ⊤ ∧
      Module.length (Localization.AtPrime q) (Localization.AtPrime q ⊗[A] M) ≠ ⊤ ∧
      Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⧸ (q.under A).map (algebraMap A (Localization.AtPrime q))) ≠ ⊤ := by
  have hp := flatGeneric_under_mem_minimalPrimes I q hq
  refine ⟨fixedSupport_localized_length_ne_top M I hI (q.under A) hp,
    flatGeneric_target_length_ne_top M I hI q hq, ?_⟩
  rw [(flatGenericClosedFiberEquiv q).length_eq]
  exact flatGeneric_target_length_ne_top (A ⧸ q.under A) I
    (by rw [Ideal.annihilator_quotient]; exact hp.le) q hq

/-- Rank-free generic length under flat base change, expressed with the
literal target localization of the base-changed module and closed fiber. -/
theorem flatGeneric_multiplicity [IsNoetherianRing A] [Module.Flat A B]
    (M : Type w) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : I ≤ Module.annihilator A M) (q : Ideal B) [q.IsPrime]
    (hq : q ∈ (I.map (algebraMap A B)).minimalPrimes) :
    Module.length (Localization.AtPrime q) (Localization.AtPrime q ⊗[B] (B ⊗[A] M)) =
      Module.length (Localization.AtPrime (q.under A))
        (Localization.AtPrime (q.under A) ⊗[A] M) *
      Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⧸ (q.under A).map (algebraMap A (Localization.AtPrime q))) := by
  rw [(flatGenericClosedFiberEquiv q).length_eq]
  exact flatGeneric_localizedBaseChange_length M I hI q hq

end Module
