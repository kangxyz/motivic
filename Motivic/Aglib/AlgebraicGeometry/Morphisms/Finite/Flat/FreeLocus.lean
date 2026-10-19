/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Finite algebra base change on the module free locus

For the original finitely presented algebra module, a basic open belongs to its
native free locus exactly when the canonical localized affine base change is
flat. Each point of the free locus consequently has a finite-flat principal
neighborhood. The algebra and its canonical structure map are unchanged apart
from this base change.

These are affine chart results, not generic-base shrinking for a proper relative
curve. In that application the two original chart opens must still be glued and
the proper image of their closed complement removed from the original base.
In particular, this file does not assume that a finite normal cover is flat.


Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.Finite.Flat.FreeLocus`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Flat.PolynomialGeneric`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace AlgebraicGeometry

universe u

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  [Module.FinitePresentation R B]

/-- The original algebra's module free locus detects flatness of its canonical
base change to a principal open. No domain or perfectness hypothesis is used. -/
theorem basicOpen_subset_freeLocus_iff_flat_specMap (r : R) :
    (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R B ↔
      Flat (Spec.map (CommRingCat.ofHom
        (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] B)))) := by
  rw [Flat.SpecMap_iff]
  change _ ↔ (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] B)).Flat
  rw [RingHom.flat_algebraMap_iff]
  let e := LocalizedModule.equivTensorProduct (Submonoid.powers r) B
  constructor
  · intro h
    let : Module.Projective (Localization.Away r) (LocalizedModule.Away r B) :=
      Module.basicOpen_subset_freeLocus_iff.mp h
    exact Module.Flat.of_linearEquiv e.symm
  · intro h
    let := h
    let : Module.Flat (Localization.Away r) (LocalizedModule.Away r B) :=
      Module.Flat.of_linearEquiv e
    exact Module.basicOpen_subset_freeLocus_iff.mpr
      (Module.freeLocus_eq_univ_iff.mp Module.freeLocus_eq_univ)

/-- Every point of the original algebra's free locus has an actual principal
neighborhood on which its canonical affine base change is finite and flat.
This chooses an element of the chart ring, not an element of a relative base. -/
theorem exists_finite_flat_specMap_away_of_mem_freeLocus
    (p : PrimeSpectrum R) (hp : p ∈ Module.freeLocus R B) :
    ∃ r : R, r ∉ p.asIdeal ∧
      IsFinite (Spec.map (CommRingCat.ofHom
        (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] B)))) ∧
      Flat (Spec.map (CommRingCat.ofHom
        (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] B)))) := by
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp
      Module.isOpen_freeLocus
  refine ⟨r, hr, ?_, (basicOpen_subset_freeLocus_iff_flat_specMap r).mp hsub⟩
  rw [IsFinite.SpecMap_iff]
  change (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] B)).Finite
  rw [RingHom.finite_algebraMap]
  infer_instance

end AlgebraicGeometry
