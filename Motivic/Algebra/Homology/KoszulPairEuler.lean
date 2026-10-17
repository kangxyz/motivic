/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulPairTor
public import Motivic.Algebra.Homology.LengthEuler
public import Motivic.RingTheory.LocalLength.KoszulPairSymmetry

/-!
# The two-equation local multiplicity is a genuine Tor Euler length

The previously constructed local integer is identified first with the Euler
characteristic of the actual Koszul chain complex. For a pair regular on the
ring, it is then identified with the alternating sum of lengths of the actual
categorical Tor modules. Finite length of every possible nonzero homology
module remains an explicit hypothesis. There is no regularity assumption on
the coefficient module in either comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Motivic.LengthEuler

universe u v

namespace Motivic.LocalLength.KoszulPair

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] (a b : R)

/-- The actual homology length support is contained in degrees zero, one and two. -/
theorem homology_length_support_subset :
    Function.support (fun n => Module.length R ((chainComplex M a b).homology n)) ⊆
      (Finset.range 3 : Set ℕ) := by
  intro n hn
  by_contra hnot
  have hn3 : 3 ≤ n := by simpa using hnot
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (exactAt_add_three M a b k)
  have : Subsingleton ((chainComplex M a b).homology (k + 3)) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  exact hn Module.length_eq_zero

/-- The three explicit local finiteness conditions certify all categorical homology. -/
theorem finiteHomology_chainComplex (h : HasFiniteHomology M a b) :
    FiniteHomology (chainComplex M a b) := by
  refine FiniteLengthSupport.of_isZero_outside _ (Finset.range 3) ?_ ?_
  · intro n hn
    have hn3 : n < 3 := Finset.mem_range.mp hn
    have hn : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hn with rfl | rfl | rfl
    · rw [(homologyZeroIso M a b).toLinearEquiv.length_eq]
      exact h.1
    · rw [(homologyOneIso M a b).toLinearEquiv.length_eq]
      exact h.2.1
    · rw [(homologyTwoIso M a b).toLinearEquiv.length_eq]
      exact h.2.2
  · intro n hn
    have hn3 : 3 ≤ n := by simpa using hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
      (exactAt_add_three M a b k)

/-- The local multiplicity is the Euler length of the actual Koszul chain homology. -/
theorem chainEuler_eq_eulerMultiplicity (h : HasFiniteHomology M a b) :
    chainEuler (chainComplex M a b) (finiteHomology_chainComplex M a b h) =
      eulerMultiplicity M a b h := by
  change signedLengthSum _ _ _ = _
  rw [signedLengthSum_eq_sum _ _ _ (Finset.range 3) (homology_length_support_subset M a b)]
  simp [Finset.sum_range_succ, integerLength, eulerMultiplicity,
    (homologyZeroIso M a b).toLinearEquiv.length_eq,
    (homologyOneIso M a b).toLinearEquiv.length_eq,
    (homologyTwoIso M a b).toLinearEquiv.length_eq, sub_eq_add_neg, add_comm]

variable (N : Type u) [AddCommGroup N] [Module R N]
variable (ha : IsSMulRegular R a) (hb : IsSMulRegular (PrincipalQuotient R a) b)

include ha hb

/-- A ring-regular pair and finite explicit Koszul homology certify finite Tor support. -/
theorem finiteLengthSupport_tor (h : HasFiniteHomology N a b) :
    FiniteLengthSupport (fun n =>
      ((Tor (ModuleCat R) n).obj (ModuleCat.of R N)).obj (ModuleCat.of R (H₀ R a b))) :=
  (finiteHomology_chainComplex N a b h).of_iso
    (fun n => (torIsoHomology N a b ha hb n).symm)

/-- The local coefficient is the alternating sum of genuine Tor lengths.
The pair is regular on the ring, while the module may have nonzero higher Tor. -/
theorem torEuler_eq_eulerMultiplicity (h : HasFiniteHomology N a b) :
    signedLengthSum (fun n =>
      ((Tor (ModuleCat R) n).obj (ModuleCat.of R N)).obj (ModuleCat.of R (H₀ R a b)))
      (fun n => (-1) ^ n) (finiteLengthSupport_tor a b N ha hb h) =
      eulerMultiplicity N a b h := by
  calc
    _ = chainEuler (chainComplex N a b) (finiteHomology_chainComplex N a b h) :=
      signedLengthSum_eq_of_iso _ _ _ (fun n => torIsoHomology N a b ha hb n)
    _ = _ := chainEuler_eq_eulerMultiplicity N a b h

end Motivic.LocalLength.KoszulPair
