/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # Monic punctured opens after shrinking the original base -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry Polynomial
universe u
namespace AlgebraicGeometry.AffineLineOpenMonicShrinking

/-- Remove precisely the zero-root factor, invert its remaining leading and constant
coefficients, and retain an actual principal-open inclusion. -/
theorem exists_monic_punctured_basicOpen (R : Type u) [CommRing R] [IsDomain R]
    (p : R[X]) (hp : p ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ ∃ g : (Localization.Away r)[X], g.Monic ∧ IsUnit (g.coeff 0) ∧
      PrimeSpectrum.basicOpen (X * g) ≤
        PrimeSpectrum.basicOpen (p.map (algebraMap R (Localization.Away r))) := by
  classical
  obtain ⟨h, he, hh⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp 0
  simp only [map_zero, sub_zero] at he hh
  have h0 : h.coeff 0 ≠ 0 := by simpa only [X_dvd_iff] using hh
  have hn : h ≠ 0 := by intro hz; exact h0 (hz ▸ coeff_zero 0)
  let r := h.leadingCoeff * h.coeff 0
  have hr : r ≠ 0 := mul_ne_zero (leadingCoeff_ne_zero.mpr hn) h0
  let S := Localization.Away r
  let : IsDomain S := Localization.Away.isDomain hr
  have hl : IsUnit (algebraMap R S h.leadingCoeff) :=
    IsLocalization.Away.isUnit_of_dvd r (dvd_mul_right _ _)
  have hc : IsUnit (algebraMap R S (h.coeff 0)) :=
    IsLocalization.Away.isUnit_of_dvd r (dvd_mul_left _ _)
  have hln := hl.ne_zero
  obtain ⟨u, hu⟩ := hl
  let g : S[X] := C (↑(u⁻¹) : S) * h.map (algebraMap R S)
  have hg : g.Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [leadingCoeff_map_of_leadingCoeff_ne_zero _ hln, ← hu]
    simp
  refine ⟨r, hr, g, hg, ?_, ?_⟩
  · change IsUnit (g.coeff 0)
    rw [show g = C (↑(u⁻¹) : S) * h.map (algebraMap R S) from rfl,
      coeff_C_mul, coeff_map]
    exact (u⁻¹).isUnit.mul hc
  · change PrimeSpectrum.basicOpen (X * g) ≤
      PrimeSpectrum.basicOpen (p.map (algebraMap R S))
    rw [he, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
    simp only [g, PrimeSpectrum.basicOpen_mul]
    exact inf_le_inf (PrimeSpectrum.le_basicOpen_pow X _) inf_le_right

/-- The map and open are the original ones. No replacement of `W` or localization
model of `W` is made; only the base is restricted by the supplied nonzero `r`. -/
theorem exists_monic_punctured_open (R : Type u) [CommRing R] [IsDomain R]
    (W : (Spec (.of R[X])).Opens) (hW : (W : Set (Spec (.of R[X]))).Nonempty) :
    ∃ r : R, r ≠ 0 ∧ ∃ g : (Localization.Away r)[X], g.Monic ∧ IsUnit (g.coeff 0) ∧
      PrimeSpectrum.basicOpen (X * g) ≤
        (Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (algebraMap R (Localization.Away r))))) ⁻¹ᵁ W := by
  obtain ⟨x, hx⟩ := hW
  obtain ⟨_, ⟨p, rfl⟩, hp, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp W.isOpen x hx
  have hp0 : p ≠ 0 := by
    intro hz
    exact hp (hz ▸ x.asIdeal.zero_mem)
  obtain ⟨r, hr, g, hg, hg0, hgp⟩ := exists_monic_punctured_basicOpen R p hp0
  refine ⟨r, hr, g, hg, hg0, ?_⟩
  intro y hy
  apply hsub
  exact hgp hy

/-- A unit constant coefficient gives actual Bézout coprimality over any coefficient ring. -/
theorem isCoprime_X_of_coeff_zero_isUnit {R : Type u} [CommRing R]
    (g : R[X]) (hg : IsUnit (g.coeff 0)) : IsCoprime X g := by
  obtain ⟨u, hu⟩ := hg
  refine ⟨-C (↑(u⁻¹) : R) * g.divX, C (↑(u⁻¹) : R), ?_⟩
  have he : g - X * g.divX = C (g.coeff 0) := by
    exact sub_eq_iff_eq_add.mpr ((X_mul_divX_add g).symm.trans (add_comm _ _))
  calc
    (-C (↑(u⁻¹) : R) * g.divX) * X + C (↑(u⁻¹) : R) * g =
        C (↑(u⁻¹) : R) * (g - X * g.divX) := by ring
    _ = 1 := by rw [he, ← map_mul, ← hu]; simp

/-- The actual moving-pair input, on the original open and after only base shrinking. -/
theorem exists_coprime_monic_punctured_open (R : Type u) [CommRing R] [IsDomain R]
    (W : (Spec (.of R[X])).Opens) (hW : (W : Set (Spec (.of R[X]))).Nonempty) :
    ∃ r : R, r ≠ 0 ∧ ∃ g : (Localization.Away r)[X], g.Monic ∧ IsUnit (g.coeff 0) ∧
      IsCoprime X g ∧ PrimeSpectrum.basicOpen (X * g) ≤
        (Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (algebraMap R (Localization.Away r))))) ⁻¹ᵁ W := by
  obtain ⟨r, hr, g, hg, hg0, hWg⟩ := exists_monic_punctured_open R W hW
  exact ⟨r, hr, g, hg, hg0, isCoprime_X_of_coeff_zero_isUnit g hg0, hWg⟩

end AlgebraicGeometry.AffineLineOpenMonicShrinking
