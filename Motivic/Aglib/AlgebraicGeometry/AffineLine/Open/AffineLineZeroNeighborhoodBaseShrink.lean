/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # A zero-point neighborhood becomes a whole-zero neighborhood after actual base restriction -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
universe u
namespace AlgebraicGeometry.Scheme

/-- Literal polynomial coefficient extension commutes with the actual zero section. -/
theorem polynomial_zero_scalar_naturality {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) =
    Spec.map (CommRingCat.ofHom f) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext <;> simp

/-- The original affine open need contain just the selected zero point. Restricting
only the base by a principal open then retains the whole zero section scheme-theoretically. -/
theorem exists_affine_whole_zero_base_restriction (R : Type u) [CommRing R]
    (O : (Spec (.of R[X])).Opens) (hO : IsAffineOpen O) (s : PrimeSpectrum R)
    (hs : Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) s ∈ O) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
      IsAffineOpen ((Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (algebraMap R (Localization.Away r))))) ⁻¹ᵁ O) ∧
      Set.range (Spec.map (CommRingCat.ofHom
        (Polynomial.evalRingHom (0 : Localization.Away r)))) ⊆
        ((Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (algebraMap R (Localization.Away r))))) ⁻¹ᵁ O) := by
  let T := (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⁻¹ᵁ O
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp T.isOpen s hs
  refine ⟨r, hr, hO.preimage _, ?_⟩
  rintro _ ⟨y, rfl⟩
  have hy : Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) y ∈
      PrimeSpectrum.basicOpen r := by
    change PrimeSpectrum.comap (algebraMap R (Localization.Away r)) y ∈
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R))
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact ⟨y, rfl⟩
  have hz := congrArg (fun g => g y)
    (polynomial_zero_scalar_naturality (algebraMap R (Localization.Away r)))
  change Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
    (algebraMap R (Localization.Away r))))
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : Localization.Away r))) y) ∈ O
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at hz
  rw [hz]
  exact hsub hy

end AlgebraicGeometry.Scheme
