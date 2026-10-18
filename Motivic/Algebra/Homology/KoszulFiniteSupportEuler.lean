/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.LocalLength.KoszulFiniteSupport
public import Motivic.Algebra.Homology.KoszulFiniteTor
public import Motivic.Algebra.Homology.LengthEuler

/-!
# Genuine finite Koszul and Tor Euler lengths from support

The proved coefficient-support criterion and degree bound establish finite
length and finite support for the actual Koszul homology. This constructs the
evidence required by the genuine length Euler characteristic. Under ambient
weak regularity the same evidence transfers to actual categorical Tor, and the
alternating Tor-length sum agrees with the coefficient Koszul Euler length.
The coefficient module remains arbitrary apart from finite generation.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open Motivic.LengthEuler

namespace Motivic.Koszul

variable {R : Type u} [CommRing R]

/-- The actual nonzero homology lengths lie in degrees zero through the list length. -/
theorem coefficient_homology_length_support_subset (M : ModuleCat R) (s : List R) :
    Function.support (fun n => Module.length R ((coefficientComplex M s).homology n)) ⊆
      (Finset.range (s.length + 1) : Set ℕ) := by
  intro n hn
  by_contra hnot
  have hbound : s.length < n := by simpa using hnot
  have : Subsingleton ((coefficientComplex M s).homology n) :=
    ModuleCat.subsingleton_of_isZero
      (HomologicalComplex.ExactAt.of_isZero (coefficient_isZero_X M s n hbound)).isZero_homology
  exact hn Module.length_eq_zero

/-- An Artinian quotient on coefficient support constructs genuine finite-length
homology support; neither kind of finiteness is assumed as target data. -/
theorem finiteHomology_of_artinian_support_quotient [IsNoetherianRing R]
    (M : ModuleCat R) [Module.Finite R M] (s : List R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ Module.annihilator R M))] :
    FiniteHomology (coefficientComplex M s) where
  finite_length :=
    Module.KoszulFinite.length_homology_ne_top_of_artinian_support_quotient M s
  finite_support := (Finset.range (s.length + 1)).finite_toSet.subset
    (coefficient_homology_length_support_subset M s)

/-- Minimality at the local coefficient support also constructs the finite
homology evidence used by the Euler length API. -/
theorem finiteHomology_of_mem_minimalPrimes_support [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat R) [Module.Finite R M] (s : List R)
    (hm : IsLocalRing.maximalIdeal R ∈
      (Ideal.ofList s ⊔ Module.annihilator R M).minimalPrimes) :
    FiniteHomology (coefficientComplex M s) where
  finite_length :=
    Module.KoszulFinite.length_homology_ne_top_of_mem_minimalPrimes_support M s hm
  finite_support := (Finset.range (s.length + 1)).finite_toSet.subset
    (coefficient_homology_length_support_subset M s)

/-- Under ambient weak regularity the equations and coefficient support also
annihilate every genuine categorical Tor module. -/
theorem support_le_annihilator_finiteTor (M : ModuleCat R) (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (n : ℕ) :
    Ideal.ofList s ⊔ Module.annihilator R M ≤ Module.annihilator R
      (((Tor (ModuleCat R) n).obj M).obj (ModuleCat.of R (R ⧸ Ideal.ofList s))) :=
  (support_le_annihilator_coefficient_homology M s n).trans
    ((finiteTorIsoHomology M s hs n).hom.hom.annihilator_le_of_injective
      ((ModuleCat.mono_iff_injective _).mp inferInstance))

variable [IsNoetherianRing R] (M : ModuleCat R) [Module.Finite R M] (s : List R)
variable [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ Module.annihilator R M))]

/-- Support hypotheses make the actual coefficient Euler length a finite sum
with its canonical list-length bound. -/
theorem chainEuler_eq_sum_of_artinian_support_quotient :
    chainEuler (coefficientComplex M s) (finiteHomology_of_artinian_support_quotient M s) =
      ∑ n ∈ Finset.range (s.length + 1), (-1 : ℤ) ^ n *
        integerLength ((coefficientComplex M s).homology n)
          ((finiteHomology_of_artinian_support_quotient M s).finite_length n) :=
  signedLengthSum_eq_sum _ _ _ _ (coefficient_homology_length_support_subset M s)

/-- Ambient weak regularity and the proved support criterion give finite support
of genuine Tor lengths, without regularity on the coefficient module. -/
theorem finiteLengthSupport_finiteTor_of_artinian_support_quotient
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    FiniteLengthSupport (fun n =>
      ((Tor (ModuleCat R) n).obj M).obj (ModuleCat.of R (R ⧸ Ideal.ofList s))) :=
  (finiteHomology_of_artinian_support_quotient M s).of_iso
    (fun n => (finiteTorIsoHomology M s hs n).symm)

/-- Genuine finite Tor Euler length agrees with the actual Koszul Euler length;
all finite-length evidence is derived from the coefficient support. -/
theorem finiteTorEuler_eq_chainEuler_of_artinian_support_quotient
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    signedLengthSum (fun n =>
      ((Tor (ModuleCat R) n).obj M).obj (ModuleCat.of R (R ⧸ Ideal.ofList s)))
      (fun n => (-1 : ℤ) ^ n) (finiteLengthSupport_finiteTor_of_artinian_support_quotient M s hs) =
      chainEuler (coefficientComplex M s) (finiteHomology_of_artinian_support_quotient M s) :=
  signedLengthSum_eq_of_iso _ _ _ (fun n => finiteTorIsoHomology M s hs n)

end Motivic.Koszul
