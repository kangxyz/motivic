/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulPairResolution
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# The two-generated ideal and its Koszul resolution

The image of the ring Koszul differential is proved equal to the actual ideal
`Ideal.span {a,b}`. Consequently the proved resolution has the genuine ideal
quotient `R / Ideal.span {a,b}` as its augmentation target, up to the explicit
quotient identification. The ideal is not substituted by unrelated abstract data.
-/

@[expose] public section

universe u

open CategoryTheory

namespace Motivic.LocalLength.KoszulPair

variable {R : Type u} [CommRing R] (a b : R)

/-- The image of the degree-one ring differential is the two-generated ideal. -/
theorem range_d₁_ring : LinearMap.range (d₁ R a b) = Ideal.span ({a, b} : Set R) := by
  ext r
  rw [LinearMap.mem_range, Ideal.mem_span_pair]
  constructor
  · rintro ⟨⟨x, y⟩, h⟩
    exact ⟨x, y, by simpa only [d₁_apply, smul_eq_mul, mul_comm] using h⟩
  · rintro ⟨x, y, h⟩
    exact ⟨(x, y), by simpa only [d₁_apply, smul_eq_mul, mul_comm] using h⟩

/-- The ring Koszul quotient is the genuine quotient by the ideal `(a,b)`. -/
noncomputable def idealQuotientEquiv : H₀ R a b ≃ₗ[R] R ⧸ Ideal.span ({a, b} : Set R) :=
  Submodule.quotEquivOfEq _ _ (range_d₁_ring a b)

/-- The proved projective resolution with the genuine two-generated ideal quotient as target. -/
noncomputable def idealProjectiveResolution (ha : IsSMulRegular R a)
    (hb : IsSMulRegular (PrincipalQuotient R a) b) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.span ({a, b} : Set R))) where
  complex := (projectiveResolution R a b ha hb).complex
  π := (projectiveResolution R a b ha hb).π ≫
    (ChainComplex.single₀ (ModuleCat R)).map (idealQuotientEquiv a b).toModuleIso.hom

end Motivic.LocalLength.KoszulPair
