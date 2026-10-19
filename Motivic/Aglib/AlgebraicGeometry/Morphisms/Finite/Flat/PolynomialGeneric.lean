/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Flat.FreeLocus
public import Motivic.Aglib.RingTheory.Localization.FreeTensor
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Finite flat polynomial algebras after a coefficient localization

A finite-presentation algebra module over `R[X]` whose generic coefficient base
change is torsion-free over `K[X]` becomes finite flat after inverting one
nonzero element of `R`. The denominator is a coefficient, not an arbitrary
polynomial, so the entire affine line over the retained base open is preserved.

The proof first uses the PID `K[X]`, then descends its finite basis through the
image of the nonzero coefficient submonoid. The conclusion uses the literal
canonical map over `(Localization.Away r)[X]`, not an unrelated flat model.
Generic torsion-freeness is an explicit hypothesis: deriving it for an actual
normal compactification requires dominance of its retained generic components.


Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.Finite.Flat.PolynomialGeneric`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Normalization.FiniteCurve.PolynomialFiniteFlat`.
-/

@[expose] public noncomputable section

open scoped Polynomial TensorProduct nonZeroDivisors

attribute [local instance] Polynomial.algebra

namespace AlgebraicGeometry

universe u

/-- Generic torsion-freeness over the polynomial PID gives finite flatness on
one whole original affine-line chart after shrinking only the coefficient base.
The actual localized polynomial module is also free. -/
theorem exists_finite_flat_polynomial_specMap_away
    (R K B : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing B] [Algebra R[X] B]
    [Module.FinitePresentation R[X] B]
    [Module.IsTorsionFree K[X] (K[X] ⊗[R[X]] B)] :
    ∃ r : R, r ≠ 0 ∧
      Module.Free (Localization.Away (Polynomial.C r))
        (LocalizedModule.Away (Polynomial.C r) B) ∧
      IsFinite (Spec.map (CommRingCat.ofHom
        (R := (Localization.Away r)[X]) (S := (Localization.Away r)[X] ⊗[R[X]] B)
        (algebraMap (Localization.Away r)[X] ((Localization.Away r)[X] ⊗[R[X]] B)))) ∧
      Flat (Spec.map (CommRingCat.ofHom
        (R := (Localization.Away r)[X]) (S := (Localization.Away r)[X] ⊗[R[X]] B)
        (algebraMap (Localization.Away r)[X] ((Localization.Away r)[X] ⊗[R[X]] B)))) := by
  let S : Submonoid R[X] := R⁰.map Polynomial.C
  let : IsLocalization S K[X] := Polynomial.isLocalization R⁰ K
  obtain ⟨f, hf, hfree, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers S
      (TensorProduct.mk R[X] K[X] B 1) K[X]
  obtain ⟨r, hr, rfl⟩ := hf
  let : Module.Free (Localization.Away (Polynomial.C r))
      (LocalizedModule.Away (Polynomial.C r) B) := hfree
  let A := (Localization.Away r)[X]
  let : IsLocalization.Away (Polynomial.C r) A := by
    simpa only [Submonoid.map_powers] using
      (Polynomial.isLocalization (Submonoid.powers r) (Localization.Away r))
  have hsub : (PrimeSpectrum.basicOpen (Polynomial.C r) : Set (PrimeSpectrum R[X])) ⊆
      Module.freeLocus R[X] B :=
    Module.basicOpen_subset_freeLocus_iff.mpr inferInstance
  have hall : Module.freeLocus A (A ⊗[R[X]] B) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro p
    apply Module.comap_freeLocus_le
    apply hsub
    rw [← PrimeSpectrum.localization_away_comap_range A (Polynomial.C r)]
    exact ⟨p, rfl⟩
  let : Module.Projective A (A ⊗[R[X]] B) := Module.freeLocus_eq_univ_iff.mp hall
  refine ⟨r, nonZeroDivisors.ne_zero hr, hfree, ?_, ?_⟩
  · rw [IsFinite.SpecMap_iff]
    change RingHom.Finite (A := A) (B := A ⊗[R[X]] B) (algebraMap A _)
    rw [RingHom.finite_algebraMap]
    infer_instance
  · rw [Flat.SpecMap_iff]
    change RingHom.Flat (R := A) (S := A ⊗[R[X]] B) (algebraMap A _)
    rw [RingHom.flat_algebraMap_iff]
    infer_instance

/-- The actual coefficient-localized tensor algebra is finite free over the
whole polynomial chart, using the same coefficient denominator as the descent. -/
theorem exists_free_polynomial_tensorProduct_away
    (R K B : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing B] [Algebra R[X] B]
    [Module.FinitePresentation R[X] B]
    [Module.IsTorsionFree K[X] (K[X] ⊗[R[X]] B)] :
    ∃ r : R, r ≠ 0 ∧
      Module.Free (Localization.Away r)[X] ((Localization.Away r)[X] ⊗[R[X]] B) := by
  obtain ⟨r, hr, hfree, _, _⟩ := exists_finite_flat_polynomial_specMap_away R K B
  let : Module.Free (Localization.Away (Polynomial.C r))
      (LocalizedModule.Away (Polynomial.C r) B) := hfree
  let : IsLocalization.Away (Polynomial.C r) (Localization.Away r)[X] := by
    simpa only [Submonoid.map_powers] using
      (Polynomial.isLocalization (Submonoid.powers r) (Localization.Away r))
  exact ⟨r, hr, Module.free_tensorProduct_of_free_localizedModule
    (Submonoid.powers (Polynomial.C r))⟩

end AlgebraicGeometry
