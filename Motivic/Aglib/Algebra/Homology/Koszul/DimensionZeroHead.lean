/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.DimensionCancellation
public import Mathlib.RingTheory.KrullDimension.Module

/-!
# Vanishing for zero coefficients and an annihilating head equation

An annihilating first equation can be removed from the support ideal. The
Artinian support quotient therefore gives finite homology for the tail, and
the actual two-column Euler cancellation proves zero Euler characteristic.
This includes the prime-quotient branch where the head belongs to the prime.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits _root_.HomologicalComplex.ModuleLengthEuler

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]

/-- Subsingleton coefficients give zero genuine Euler characteristic for every
list, with any supplied finite-homology evidence. -/
theorem koszulDimension_chainEuler_zero_of_subsingleton (M : ModuleCat R) [Subsingleton M]
    (s : List R) (h : FiniteHomology (coefficientComplex M s)) :
    chainEuler (coefficientComplex M s) h = 0 := by
  have hzero : IsZero (coefficientComplex M s) :=
    Functor.map_isZero (coefficientFunctor s) (ModuleCat.isZero_of_subsingleton M)
  have hhom (n : ℕ) : Subsingleton ((coefficientComplex M s).homology n) :=
    ModuleCat.subsingleton_of_isZero
      (Functor.map_isZero (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n)
        hzero)
  change (∑ᶠ n, (-1 : ℤ) ^ n * integerLength _ _) = 0
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  have := hhom n
  simp [integerLength]

/-- Negative support dimension is exactly the empty-module base case needed
for induction on an arbitrary equation list. -/
theorem koszulDimension_chainEuler_zero_of_supportDim_lt_zero (M : ModuleCat R)
    (s : List R) (hd : Module.supportDim R M < 0)
    (h : FiniteHomology (coefficientComplex M s)) :
    chainEuler (coefficientComplex M s) h = 0 := by
  have : Subsingleton M := Module.supportDim_eq_bot_iff_subsingleton R M |>.mp
    ((WithBot.lt_zero_iff_eq_bot _).mp hd)
  exact koszulDimension_chainEuler_zero_of_subsingleton M s h

/-- An equation that already annihilates the coefficients does not change the
support ideal formed from the remaining equations and the annihilator. -/
theorem koszulDimension_supportIdeal_cons_of_mem_annihilator (M : ModuleCat R)
    (a : R) (s : List R) (ha : a ∈ Module.annihilator R M) :
    Ideal.ofList (a :: s) ⊔ Module.annihilator R M =
      Ideal.ofList s ⊔ Module.annihilator R M := by
  have hspan : Ideal.span {a} ≤ Module.annihilator R M :=
    (Ideal.span_singleton_le_iff_mem _).mpr ha
  rw [Ideal.ofList_cons, sup_comm (Ideal.span {a}), sup_assoc, sup_eq_right.mpr hspan]

/-- An annihilating head equation forces actual all-degree Koszul Euler
vanishing, with tail finiteness derived from the Artinian support quotient. -/
theorem koszulDimension_chainEuler_zero_of_mem_annihilator [IsNoetherianRing R]
    (M : ModuleCat R) [Module.Finite R M] (a : R) (s : List R)
    (ha : a ∈ Module.annihilator R M)
    [IsArtinianRing (R ⧸ (Ideal.ofList (a :: s) ⊔ Module.annihilator R M))] :
    chainEuler (coefficientComplex M (a :: s))
      (finiteHomology_of_artinian_support_quotient M (a :: s)) = 0 := by
  have : IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ Module.annihilator R M)) := by
    rw [← koszulDimension_supportIdeal_cons_of_mem_annihilator M a s ha]
    infer_instance
  exact koszulDimensionTensor_chainEuler_zero a (coefficientComplex M s)
    (finiteHomology_of_artinian_support_quotient M s)

end ChainComplex.Koszul
