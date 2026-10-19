/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.HyperhomologyTail
public import Motivic.Aglib.Algebra.Homology.Koszul.HyperhomologyPlacement

/-!
# Bounded Koszul hyperhomology Euler comparison

For an actual nonnegative complex with bounded homology, finiteness is required
only after applying the coefficient Koszul complex to each surviving homology
module. Induction through the actual canonical tail and truncation sequence
proves finite homology of the total tensor and its alternating homology-layer
Euler formula. In particular neither the original homology nor the chain
terms are required to have finite length.
-/

@[expose] public section

universe u

open CategoryTheory HomologicalComplex _root_.HomologicalComplex.ModuleLengthEuler

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]

/-- The bounded hyperhomology Euler formula for the actual finite Koszul tensor.
The finite sum runs over exactly the homology degrees zero through `N`. -/
theorem bounded_koszulTensor_chainEuler (K : ChainComplex (ModuleCat R) ℕ)
    (s : List R) (N : ℕ) (hK : ∀ n, N < n → K.ExactAt n)
    (hH : ∀ n, n ≤ N → FiniteHomology (coefficientComplex (K.homology n) s)) :
    ∃ h : FiniteHomology (tensorObj (chainComplex s) K),
      chainEuler (tensorObj (chainComplex s) K) h =
        ∑ n : Fin (N + 1), (-1 : ℤ) ^ (n : ℕ) *
          chainEuler (coefficientComplex (K.homology n) s) (hH n (by omega)) := by
  induction N generalizing K with
  | zero =>
    refine ⟨degreeZeroTensor_finiteHomology K s (fun n => hK (n + 1) (by omega))
      (hH 0 (by omega)), ?_⟩
    simpa using degreeZeroTensor_chainEuler K s
      (fun n => hK (n + 1) (by omega)) (hH 0 (by omega))
  | succ N ih =>
    let hTailH : ∀ n, n ≤ N →
        FiniteHomology (coefficientComplex ((homologyTail K).homology n) s) :=
      fun n hn => homologyTailCoefficient_finiteHomology K s n (hH (n + 1) (by omega))
    obtain ⟨hTail, eTail⟩ := ih (homologyTail K)
      (homologyTail_exactAt_above K N hK) hTailH
    let hPlaced := koszulTensor_placement_finiteHomology (homologyTail K) s hTail
    let hTrunc := hPlaced.of_quasiIso (homologyTailTensorTruncationIso K s).inv
    obtain ⟨hTotal, eTotal⟩ := firstTruncation_chainEuler K s hTrunc (hH 0 (by omega))
    refine ⟨hTotal, ?_⟩
    have eTrunc : chainEuler (tensorObj (chainComplex s) (K.truncLE (chainPlacement 1)))
        hTrunc = -chainEuler (tensorObj (chainComplex s) (homologyTail K)) hTail := by
      exact (homologyEuler_eq_of_quasiIso (homologyTailTensorTruncationIso K s).hom
        (fun n => (-1 : ℤ) ^ n) hTrunc hPlaced).trans
        (koszulTensor_placement_chainEuler (homologyTail K) s hTail)
    rw [eTotal, eTrunc, eTail]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ]
    rw [add_comm]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [homologyTailCoefficient_chainEuler K s n (hH (n + 1) (by omega)), pow_succ]
    ring

/-- Finite coefficient-Koszul homology on the bounded homology layers derives
finite homology of the actual total tensor. -/
theorem bounded_koszulTensor_finiteHomology (K : ChainComplex (ModuleCat R) ℕ)
    (s : List R) (N : ℕ) (hK : ∀ n, N < n → K.ExactAt n)
    (hH : ∀ n, n ≤ N → FiniteHomology (coefficientComplex (K.homology n) s)) :
    FiniteHomology (tensorObj (chainComplex s) K) :=
  (bounded_koszulTensor_chainEuler K s N hK hH).choose

/-- The bounded formula with its derived finite-homology evidence made explicit. -/
theorem bounded_koszulTensor_chainEuler_eq (K : ChainComplex (ModuleCat R) ℕ)
    (s : List R) (N : ℕ) (hK : ∀ n, N < n → K.ExactAt n)
    (hH : ∀ n, n ≤ N → FiniteHomology (coefficientComplex (K.homology n) s)) :
    chainEuler (tensorObj (chainComplex s) K)
        (bounded_koszulTensor_finiteHomology K s N hK hH) =
      ∑ n : Fin (N + 1), (-1 : ℤ) ^ (n : ℕ) *
        chainEuler (coefficientComplex (K.homology n) s) (hH n (by omega)) :=
  (bounded_koszulTensor_chainEuler K s N hK hH).choose_spec

/-- For a finite coefficient module, the common equation-support quotient
constructs the later Koszul finiteness of every actual first-stage homology. -/
theorem coefficient_homology_koszul_finiteHomology [IsNoetherianRing R]
    (M : ModuleCat R) [Module.Finite R M] (s t : List R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔
      (Ideal.ofList t ⊔ Module.annihilator R M)))] (n : ℕ) :
    FiniteHomology (coefficientComplex ((coefficientComplex M t).homology n) s) :=
  finiteHomology_of_artinian_quotient_of_le_annihilator
    ((coefficientComplex M t).homology n) s
    (Ideal.ofList t ⊔ Module.annihilator R M)
    (support_le_annihilator_coefficient_homology M t n)

/-- The genuine two-stage Koszul Euler formula from an Artinian final support
quotient. Finite generation of the original coefficient module is explicit;
its length and the first-stage homology lengths need not be finite. -/
theorem coefficient_koszulTensor_chainEuler [IsNoetherianRing R]
    (M : ModuleCat R) [Module.Finite R M] (s t : List R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔
      (Ideal.ofList t ⊔ Module.annihilator R M)))] :
    ∃ h : FiniteHomology (tensorObj (chainComplex s) (coefficientComplex M t)),
      chainEuler (tensorObj (chainComplex s) (coefficientComplex M t)) h =
        ∑ n : Fin (t.length + 1), (-1 : ℤ) ^ (n : ℕ) *
          chainEuler (coefficientComplex ((coefficientComplex M t).homology n) s)
            (coefficient_homology_koszul_finiteHomology M s t n) :=
  bounded_koszulTensor_chainEuler (coefficientComplex M t) s t.length
    (fun n hn => ExactAt.of_isZero (coefficient_isZero_X M t n hn))
    (fun n _ => coefficient_homology_koszul_finiteHomology M s t n)

end ChainComplex.Koszul
