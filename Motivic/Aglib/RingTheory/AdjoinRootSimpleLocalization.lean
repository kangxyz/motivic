/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Polynomial.Tower

/-!
# Actual local lengths at a simple split polynomial root

The original quotient localization is retained. When its adjoined coordinate
becomes a scalar, its scalar map is bijective and its self-length is one.
For `(X - 1)^m * (X - a)`, the repeated factor becomes a unit at the branch
with residual coordinate `a ≠ 1`; no reduction of the quotient is performed.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

universe u

variable {k : Type u} [Field k]

/-- A localization of a polynomial quotient whose coordinate is a base scalar
has a surjective literal base-field map. -/
theorem localization_algebraMap_surjective_of_root_eq {p : k[X]}
    (q : PrimeSpectrum (AdjoinRoot p)) (a : k)
    (ha : algebraMap (AdjoinRoot p) (Localization.AtPrime q.asIdeal) (root p) =
      algebraMap k (Localization.AtPrime q.asIdeal) a) :
    Function.Surjective (algebraMap k (Localization.AtPrime q.asIdeal)) := by
  let R := AdjoinRoot p
  let L := Localization.AtPrime q.asIdeal
  have hscalar : ∀ r : R, ∃ c : k, algebraMap R L r = algebraMap k L c := by
    intro r
    obtain ⟨g, rfl⟩ := mk_surjective r
    refine ⟨g.eval a, ?_⟩
    rw [← aeval_eq, ← aeval_algebraMap_apply, ha,
      aeval_algebraMap_apply_eq_algebraMap_eval]
  intro z
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq q.asIdeal.primeCompl z
  obtain ⟨c, hc⟩ := hscalar r
  obtain ⟨d, hd⟩ := hscalar s
  have hd0 : d ≠ 0 := by
    intro h
    have hu := IsLocalization.map_units L s
    rw [hd, h, map_zero] at hu
    exact not_isUnit_zero hu
  refine ⟨c / d, ?_⟩
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  rw [hc, hd, ← map_mul, div_mul_cancel₀ c hd0]

/-- The actual local ring has length one when its quotient coordinate is a
base scalar. The proof uses its original base-field map. -/
theorem local_length_eq_one_of_root_eq {p : k[X]}
    (q : PrimeSpectrum (AdjoinRoot p)) (a : k)
    (ha : algebraMap (AdjoinRoot p) (Localization.AtPrime q.asIdeal) (root p) =
      algebraMap k (Localization.AtPrime q.asIdeal) a) :
    Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) = 1 := by
  let L := Localization.AtPrime q.asIdeal
  have hsurj := localization_algebraMap_surjective_of_root_eq q a ha
  let e : k ≃ₐ[k] L := AlgEquiv.ofBijective (Algebra.ofId k L)
    ⟨(algebraMap k L).injective, hsurj⟩
  rw [← Module.length_eq_of_surjective hsurj, ← e.toLinearEquiv.length_eq]
  exact Module.length_eq_one k k

/-- The distinct simple branch of a split polynomial has literal local
self-length one, even though the other factor may be nonreduced. -/
theorem split_simple_local_length (a : k) (ha : a ≠ 1) (m : ℕ)
    (q : MaximalSpectrum (AdjoinRoot ((X - 1) ^ m * (X - C a))))
    (hq : Ideal.Quotient.mk q.asIdeal (root ((X - 1) ^ m * (X - C a))) =
      algebraMap k (AdjoinRoot ((X - 1) ^ m * (X - C a)) ⧸ q.asIdeal) a) :
    Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) = 1 := by
  let p : k[X] := (X - 1) ^ m * (X - C a)
  let R := AdjoinRoot p
  let L := Localization.AtPrime q.asIdeal
  let : Field (R ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal
  change Ideal.Quotient.mk q.asIdeal (root p) = algebraMap k (R ⧸ q.asIdeal) a at hq
  have hu : IsUnit (algebraMap R L (root p - 1)) := by
    apply (IsLocalization.AtPrime.isUnit_to_map_iff L q.asIdeal _).mpr
    change root p - 1 ∉ q.asIdeal
    intro h
    have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr h
    have he : algebraMap k (R ⧸ q.asIdeal) a = 1 := by
      apply sub_eq_zero.mp
      simpa only [map_sub, map_one, hq] using hz
    exact ha ((algebraMap k (R ⧸ q.asIdeal)).injective
      (he.trans (map_one _).symm))
  have hrel : (root p - 1) ^ m * (root p - algebraMap k R a) = 0 := by
    change (root p - 1) ^ m * (root p - of p a) = 0
    simpa only [p, eval₂_mul, eval₂_pow, eval₂_sub, eval₂_X, eval₂_one,
      eval₂_C, algebraMap_eq] using eval₂_root p
  have hp : (algebraMap R L (root p) - 1) ^ m *
      (algebraMap R L (root p) - algebraMap k L a) = 0 := by
    have h := congrArg (algebraMap R L) hrel
    simpa only [map_mul, map_pow, map_sub, map_one, map_zero,
      ← IsScalarTower.algebraMap_apply] using h
  have hu' : IsUnit ((algebraMap R L (root p) - 1) ^ m) := by
    simpa only [map_sub, map_one] using hu.pow m
  exact local_length_eq_one_of_root_eq q.toPrimeSpectrum a
    (sub_eq_zero.mp (hu'.mul_right_eq_zero.mp hp))

end AdjoinRoot
