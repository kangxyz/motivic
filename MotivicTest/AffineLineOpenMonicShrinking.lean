/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.AffineLineOpenMonicShrinking
public import Lean

/-! # The original open and the actual coefficient-localization map are retained -/
public noncomputable section
open AlgebraicGeometry Polynomial AlgebraicGeometry.AffineLineOpenMonicShrinking
universe u
namespace MotivicTest.AffineLineOpenMonicShrinking

/-- Arbitrary domains and original nonempty opens, without a supplied principal presentation. -/
theorem actual_open_base_shrinking (R : Type u) [CommRing R] [IsDomain R]
    (W : (Spec (.of R[X])).Opens) (hW : (W : Set (Spec (.of R[X]))).Nonempty) :
    ∃ r : R, r ≠ 0 ∧ ∃ g : (Localization.Away r)[X], g.Monic ∧ IsUnit (g.coeff 0) ∧
      IsCoprime X g ∧ PrimeSpectrum.basicOpen (X * g) ≤
        (Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (algebraMap R (Localization.Away r))))) ⁻¹ᵁ W :=
  exists_coprime_monic_punctured_open R W hW

/-- The Bézout input works over general rings, including nonfields. -/
theorem zero_and_shift_coprime (R : Type u) [CommRing R] :
    IsCoprime (X : R[X]) (X + 1) := by
  apply isCoprime_X_of_coeff_zero_isUnit
  simp

/-- Zero roots of arbitrary multiplicity are permitted in the original equation. -/
theorem repeated_zero_roots (R : Type u) [CommRing R] [IsDomain R] (n : ℕ)
    (p : R[X]) (hp : p ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ ∃ g : (Localization.Away r)[X], g.Monic ∧ IsUnit (g.coeff 0) ∧
      PrimeSpectrum.basicOpen (X * g) ≤
        PrimeSpectrum.basicOpen ((X ^ n * p).map (algebraMap R (Localization.Away r))) :=
  exists_monic_punctured_basicOpen R (X ^ n * p) (mul_ne_zero (pow_ne_zero _ X_ne_zero) hp)

open Lean in
run_cmd do
  for name in #[``actual_open_base_shrinking, ``zero_and_shift_coprime, ``repeated_zero_roots,
      ``exists_monic_punctured_basicOpen, ``exists_coprime_monic_punctured_open] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original open, actual base localization, monic coprime punctured subopen: audited."

end MotivicTest.AffineLineOpenMonicShrinking
