/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.LengthEulerExtendChain
public import Motivic.Algebra.Homology.KoszulCoefficientEulerAdditivity

/-!
# Actual coefficient-Koszul consumers of homological placement

The coefficients may have infinite length. Only the subsequent Koszul
homology is required to have finite length; an Artinian common support
quotient provides this evidence. Repeated and zero equations are allowed.
-/

@[expose] public section

universe u

open Motivic.LengthEuler Motivic.Koszul

namespace MotivicTest.LengthEulerExtend

variable {R : Type u} [CommRing R]

/-- The placed coefficient homology is the genuine old homology in translated degree. -/
theorem placedCoefficientHomologyLength (M : ModuleCat R) (s : List R) (q n : ℕ) :
    Module.length R (((coefficientComplex M s).extend (chainPlacement q)).homology (n + q)) =
      Module.length R ((coefficientComplex M s).homology n) :=
  length_homology_extend_image _ _ n

/-- Repetition and a zero equation give a real four-degree support interval after placement. -/
theorem repeatedZeroPlacedSupport (a : R) (M : ModuleCat R) :
    Function.support (fun n => Module.length R
      (((coefficientComplex M [a, a, 0]).extend (chainPlacement 2)).homology n)) ⊆
        (Finset.Icc 2 5 : Set ℕ) := by
  rw [support_length_homology_extend]
  rintro j ⟨i, hi, rfl⟩
  have hi' := coefficient_homology_length_support_subset M [a, a, 0] hi
  have hi'' : i < 4 := by simpa using hi'
  change i + 2 ∈ (Finset.Icc 2 5 : Finset ℕ)
  simp only [Finset.mem_Icc]
  omega

/-- An odd placement changes the actual coefficient-Koszul Euler sign. -/
theorem oddPlacedCoefficientEuler (M : ModuleCat R) (s : List R)
    (h : FiniteHomology (coefficientComplex M s)) :
    chainEuler ((coefficientComplex M s).extend (chainPlacement 3))
        (h.extend (chainPlacement 3)) = -chainEuler (coefficientComplex M s) h := by
  simpa using chainEuler_extend_placement (coefficientComplex M s) 3 h

/-- Finite support of the subsequent Koszul homology suffices even when the
coefficient module itself is not assumed to have finite length. -/
theorem placedArtinianCoefficientEuler [IsNoetherianRing R]
    (M : ModuleCat R) [Module.Finite R M] (s : List R) (I : Ideal R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ I))]
    (hI : I ≤ Module.annihilator R M) (q : ℕ) :
    ∃ h : FiniteHomology ((coefficientComplex M s).extend (chainPlacement q)),
      chainEuler ((coefficientComplex M s).extend (chainPlacement q)) h =
        (-1 : ℤ) ^ q * chainEuler (coefficientComplex M s)
          (finiteHomology_of_artinian_quotient_of_le_annihilator M s I hI) :=
  ⟨(finiteHomology_of_artinian_quotient_of_le_annihilator M s I hI).extend
      (chainPlacement q),
    chainEuler_extend_placement _ q _⟩

end MotivicTest.LengthEulerExtend
