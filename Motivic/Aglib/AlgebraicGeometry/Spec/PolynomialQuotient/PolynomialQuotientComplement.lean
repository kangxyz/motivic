/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.PolynomialOpenQuotient

/-! # The full polynomial quotient is the complement of its principal open -/

@[expose] public noncomputable section
open AlgebraicGeometry Polynomial
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient

/-- The original whole quotient has the full complement as its underlying image.
There is no passage to the reduced quotient. -/
theorem range_inclusion_complement {R : Type u} [CommRing R] (f : R[X]) :
    Set.range (inclusion f) = (principalOpen f : Set (Spec (.of R[X])))ᶜ := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {f}))) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, PrimeSpectrum.zeroLocus_span]
  ext x
  simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
  change f ∈ x.asIdeal ↔ ¬¬ f ∈ x.asIdeal
  exact not_not.symm

end AlgebraicGeometry.PolynomialOpenQuotient
