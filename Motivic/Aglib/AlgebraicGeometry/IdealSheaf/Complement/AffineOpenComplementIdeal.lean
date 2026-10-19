/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The actual nonzero ideal of the complement of a nonempty affine-spectrum open -/
@[expose] public noncomputable section
open AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme
variable (R : Type u) [CommRing R] (U : (Spec (.of R)).Opens)

/-- This ideal is used only to choose the bad scheme for moving. Existing prescribed
nonreduced closed schemes are never replaced by this construction. -/
def openComplementIdeal : Ideal R := PrimeSpectrum.vanishingIdeal (U : Set (Spec (.of R)))ᶜ

/-- Exact image of the actual quotient closed immersion. -/
theorem range_openComplementIdeal :
    Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (openComplementIdeal R U)))) =
      (U : Set (Spec (.of R)))ᶜ := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (openComplementIdeal R U))) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, openComplementIdeal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  exact U.isOpen.isClosed_compl.closure_eq

/-- A nonempty good open gives a genuinely nonzero bad ideal. -/
theorem openComplementIdeal_ne_bot (hU : (U : Set (Spec (.of R))).Nonempty) :
    openComplementIdeal R U ≠ ⊥ := by
  intro h
  obtain ⟨x, hx⟩ := hU
  have he : PrimeSpectrum.zeroLocus (openComplementIdeal R U : Set R) =
      (U : Set (Spec (.of R)))ᶜ := by
    rw [openComplementIdeal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact U.isOpen.isClosed_compl.closure_eq
  rw [h, PrimeSpectrum.zeroLocus_bot] at he
  exact (he ▸ (Set.mem_univ x)) hx

end AlgebraicGeometry.Scheme
