/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.LengthEuler.Additivity

/-!
# Euler length additivity for nonnegative chain complexes

At degree zero the homology epimorphism closes the long exact sequence.
Together with cancellation of the connecting-map images, this proves Euler
length additivity for actual short exact sequences of nonnegative complexes.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace HomologicalComplex.ModuleLengthEuler

/-- Split the first term from a finitely supported sum over natural numbers. -/
theorem finsum_nat_succ (a : ℕ → ℤ) (ha : a.HasFiniteSupport) :
    (∑ᶠ n, a n) = a 0 + ∑ᶠ n, a (n + 1) := by
  let e : Option ℕ → ℕ := fun o => o.elim 0 Nat.succ
  have he : Function.Bijective e := by
    constructor
    · intro x y h
      cases x <;> cases y <;> simp_all [e]
    · intro n
      cases n with
      | zero => exact ⟨none, rfl⟩
      | succ n => exact ⟨some n, rfl⟩
  have hh := finsum_option (f := fun o => a (e o))
    (show (fun n => a (n + 1)).HasFiniteSupport from
      Function.HasFiniteSupport.fun_comp_of_injective Nat.succ_injective ha)
  rw [finsum_comp e he] at hh
  exact hh

/-- The alternating natural-number sum shifts with its degree-zero boundary term. -/
theorem alternatingNatSum_succ (a : ℕ → ℤ) (ha : a.HasFiniteSupport) :
    (∑ᶠ n, (-1 : ℤ) ^ n * a (n + 1)) =
      a 0 - ∑ᶠ n, (-1 : ℤ) ^ n * a n := by
  have hh := finsum_nat_succ (fun n => (-1 : ℤ) ^ n * a n)
    (Function.HasFiniteSupport.mul_right _ ha)
  simp only [pow_zero, one_mul, pow_succ, mul_neg_one, neg_mul,
    finsum_neg_distrib] at hh
  omega

variable {R : Type u} [Ring R]

/-- The image of a surjection has the same genuine finite length as its codomain. -/
theorem imageLength_of_surjective {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hM : Module.length R M ≠ ⊤) (hN : Module.length R N ≠ ⊤) :
    imageLength f hM = integerLength N hN := by
  simp only [imageLength, integerLength]
  rw [LinearMap.range_eq_top.mpr hf, Module.length_top]

/-- Homology Euler length is additive on an actual short exact sequence of
nonnegative chain complexes with finite-length, finitely supported homology. -/
theorem chainEuler_add_of_shortExact
    (S : ShortComplex (ChainComplex (ModuleCat.{v} R) ℕ)) (hS : S.ShortExact)
    (hA : FiniteHomology S.X₁) (hB : FiniteHomology S.X₂) (hC : FiniteHomology S.X₃) :
    chainEuler S.X₂ hB = chainEuler S.X₁ hA + chainEuler S.X₃ hC := by
  let f := fun i => HomologicalComplex.homologyMap S.f i
  let g := fun i => HomologicalComplex.homologyMap S.g i
  let δ := fun i : ℕ => hS.δ (i + 1) i rfl
  have hf : ∀ i, Function.Exact (f i) (g i) := fun i =>
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₂ i)
  have hg : ∀ i, Function.Exact (g (i + 1)) (δ i) := fun i =>
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₃ (i + 1) i rfl)
  have hδ : ∀ i, Function.Exact (δ i) (f i) := fun i =>
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₁ (i + 1) i rfl)
  have hC' := hC.comp (fun i : ℕ => i + 1) Nat.succ_injective
  have hB' := hB.comp (fun i : ℕ => i + 1) Nat.succ_injective
  have hb := signedLengthSum_exact_pair f g hf hA hB (fun i => (-1 : ℤ) ^ i)
  have hc := signedLengthSum_exact_pair (fun i => g (i + 1)) δ hg hB' hC'
    (fun i => (-1 : ℤ) ^ i)
  have ha := signedLengthSum_exact_pair δ f hδ hC' hA (fun i => (-1 : ℤ) ^ i)
  have hepi : Epi (g 0) := by
    have := hS.epi_g
    exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0 (by
      intro j
      change ¬ j + 1 = 0
      omega)
  have hz := imageLength_of_surjective (g 0).hom
    ((ModuleCat.epi_iff_surjective (g 0)).mp hepi) (hB.finite_length 0) (hC.finite_length 0)
  have hfinC :
      (fun i => integerLength (S.X₃.homology i) (hC.finite_length i)).HasFiniteSupport := by
    simpa only [one_mul] using finiteSupport_summand _ (fun _ => 1) hC
  change (∑ᶠ i, (-1 : ℤ) ^ i * integerLength (S.X₃.homology (i + 1))
    (hC.finite_length (i + 1))) = _ at hc
  rw [alternatingNatSum_succ _ hfinC,
    alternatingNatSum_succ _ (finiteSupport_imageLength g hB)] at hc
  change chainEuler S.X₂ hB = _ at hb
  change chainEuler S.X₁ hA = _ at ha
  change _ - chainEuler S.X₃ hC = _ at hc
  omega

end HomologicalComplex.ModuleLengthEuler
