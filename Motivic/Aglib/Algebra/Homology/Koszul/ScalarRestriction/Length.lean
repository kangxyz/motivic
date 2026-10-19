/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.ScalarRestriction.Basic
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.AmbientLength

/-!
# Koszul lengths and Euler sums under a surjective scalar map

The actual cross-ring Koszul isomorphism compares module lengths when the
ring map is surjective, including arbitrary quotient maps and surjective
local maps. Finite-length support is transferred from actual evidence, never
inferred merely from the isomorphism, and no infinite length is converted to
an integer. No flatness of the quotient or coefficient module is assumed.
-/

@[expose] public section

universe u

open CategoryTheory _root_.HomologicalComplex.ModuleLengthEuler

namespace ChainComplex.Koszul

variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (hf : Function.Surjective f) (M : ModuleCat.{u} S) (s : List R)

include hf

/-- A surjective scalar map preserves the actual Koszul homology length. -/
theorem coefficientRestrict_length (n : ℕ) :
    Module.length R ((coefficientComplex ((ModuleCat.restrictScalars f).obj M) s).homology n) =
      Module.length S ((coefficientComplex M (s.map f)).homology n) :=
  (coefficientRestrictHomologyIso f M s n).toLinearEquiv.length_eq.trans
    (_root_.ModuleCat.length_restrictScalars_of_surjective f hf _)

/-- Genuine finite length and finite degree support transfer in both directions. -/
theorem coefficientRestrict_finiteLengthSupport_iff :
    FiniteLengthSupport
        (fun n ↦ (coefficientComplex ((ModuleCat.restrictScalars f).obj M) s).homology n) ↔
      FiniteLengthSupport (fun n ↦ (coefficientComplex M (s.map f)).homology n) := by
  have hlen :
      (fun n ↦ Module.length R
        ((coefficientComplex ((ModuleCat.restrictScalars f).obj M) s).homology n)) =
      fun n ↦ Module.length S ((coefficientComplex M (s.map f)).homology n) :=
    funext (coefficientRestrict_length f hf M s)
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro n
      rw [← coefficientRestrict_length f hf M s n]
      exact h.finite_length n
    · simpa only [hlen] using h.finite_support
  · intro h
    refine ⟨?_, ?_⟩
    · intro n
      rw [coefficientRestrict_length f hf M s n]
      exact h.finite_length n
    · simpa only [hlen] using h.finite_support

/-- Every finite signed Koszul Euler sum is preserved by a surjective scalar map. -/
theorem coefficientRestrict_signedLengthSum (sign : ℕ → ℤ)
    (h : FiniteLengthSupport
      (fun n ↦ (coefficientComplex ((ModuleCat.restrictScalars f).obj M) s).homology n)) :
    signedLengthSum
        (fun n ↦ (coefficientComplex ((ModuleCat.restrictScalars f).obj M) s).homology n)
        sign h =
      signedLengthSum (fun n ↦ (coefficientComplex M (s.map f)).homology n) sign
        ((coefficientRestrict_finiteLengthSupport_iff f hf M s).mp h) := by
  unfold signedLengthSum
  apply finsum_congr
  intro n
  simp only [integerLength, coefficientRestrict_length f hf M s n]

end ChainComplex.Koszul
