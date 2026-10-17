/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.AdjoinRootSimpleLocalization

/-!
# Actual local lengths at a simple linear factor

At a maximal ideal whose residual coordinate is `a`, a complementary polynomial
with nonzero value at `a` becomes a unit in the original quotient localization.
Cancelling this unit proves that the original local ring has self-length one.
No reducedness or separability assumption on the complementary factor is used.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

universe u

variable {k : Type u} [Field k]

/-- A polynomial with nonzero value at the residual coordinate becomes a unit
in the original localization of the polynomial quotient. -/
theorem localization_isUnit_mk_of_residual_root_eq {p : k[X]}
    (q : MaximalSpectrum (AdjoinRoot p)) (a : k)
    (hq : Ideal.Quotient.mk q.asIdeal (root p) =
      algebraMap k (AdjoinRoot p ⧸ q.asIdeal) a)
    (g : k[X]) (hg : g.eval a ≠ 0) :
    IsUnit (algebraMap (AdjoinRoot p) (Localization.AtPrime q.asIdeal) (mk p g)) := by
  let R := AdjoinRoot p
  let L := Localization.AtPrime q.asIdeal
  let : Field (R ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal
  have he : Ideal.Quotient.mk q.asIdeal (mk p g) =
      algebraMap k (R ⧸ q.asIdeal) (g.eval a) := by
    change algebraMap R (R ⧸ q.asIdeal) (mk p g) = _
    rw [← aeval_eq, ← aeval_algebraMap_apply]
    change aeval (Ideal.Quotient.mk q.asIdeal (root p)) g = _
    rw [hq, aeval_algebraMap_apply_eq_algebraMap_eval]
  apply (IsLocalization.AtPrime.isUnit_to_map_iff L q.asIdeal _).mpr
  intro h
  have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr h
  rw [he] at hz
  exact hg ((algebraMap k (R ⧸ q.asIdeal)).injective (hz.trans (map_zero _).symm))

/-- A simple linear factor makes the adjoined coordinate equal its residual
scalar in the original localization. -/
theorem localization_root_eq_of_simple_factor {p g : k[X]} (a : k)
    (hp : p = (X - C a) * g) (q : MaximalSpectrum (AdjoinRoot p))
    (hq : Ideal.Quotient.mk q.asIdeal (root p) =
      algebraMap k (AdjoinRoot p ⧸ q.asIdeal) a)
    (hg : g.eval a ≠ 0) :
    algebraMap (AdjoinRoot p) (Localization.AtPrime q.asIdeal) (root p) =
      algebraMap k (Localization.AtPrime q.asIdeal) a := by
  let R := AdjoinRoot p
  let L := Localization.AtPrime q.asIdeal
  have hu := localization_isUnit_mk_of_residual_root_eq q a hq g hg
  have hrel : (root p - algebraMap k R a) * mk p g = 0 := by
    change (root p - of p a) * mk p g = 0
    have hzero : mk p ((X - C a) * g) = 0 := by rw [← hp, mk_self]
    simpa only [map_mul, map_sub, mk_X, mk_C] using hzero
  have hlocal : (algebraMap R L (root p) - algebraMap k L a) *
      algebraMap R L (mk p g) = 0 := by
    have h := congrArg (algebraMap R L) hrel
    simpa only [map_mul, map_sub, map_zero, ← IsScalarTower.algebraMap_apply] using h
  exact sub_eq_zero.mp (hu.mul_left_eq_zero.mp hlocal)

/-- The original localization at a simple linear factor has self-length one,
even when the complementary factor has repeated or inseparable roots. -/
theorem simple_factor_local_length {p g : k[X]} (a : k)
    (hp : p = (X - C a) * g) (q : MaximalSpectrum (AdjoinRoot p))
    (hq : Ideal.Quotient.mk q.asIdeal (root p) =
      algebraMap k (AdjoinRoot p ⧸ q.asIdeal) a)
    (hg : g.eval a ≠ 0) :
    Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) = 1 := by
  exact local_length_eq_one_of_root_eq q.toPrimeSpectrum a
    (localization_root_eq_of_simple_factor a hp q hq hg)

/-- The left-associated product of three scalar linear factors is monic. -/
theorem three_linear_monic (a b c : k) :
    ((X - C a) * (X - C b) * (X - C c)).Monic :=
  ((monic_X_sub_C a).mul (monic_X_sub_C b)).mul (monic_X_sub_C c)

/-- Three scalar linear factors contribute degree three, including collisions. -/
theorem three_linear_natDegree (a b c : k) :
    ((X - C a) * (X - C b) * (X - C c)).natDegree = 3 := by
  rw [Monic.natDegree_mul ((monic_X_sub_C a).mul (monic_X_sub_C b))
    (monic_X_sub_C c), Monic.natDegree_mul (monic_X_sub_C a) (monic_X_sub_C b),
    natDegree_X_sub_C, natDegree_X_sub_C, natDegree_X_sub_C]

/-- Every maximal quotient of the split cubic has one of its three original
scalar coordinates, without a distinctness hypothesis. -/
theorem three_linear_residual_root (a b c : k)
    (q : MaximalSpectrum (AdjoinRoot ((X - C a) * (X - C b) * (X - C c)))) :
    Ideal.Quotient.mk q.asIdeal (root ((X - C a) * (X - C b) * (X - C c))) =
        algebraMap k (AdjoinRoot ((X - C a) * (X - C b) * (X - C c)) ⧸ q.asIdeal) a ∨
      Ideal.Quotient.mk q.asIdeal (root ((X - C a) * (X - C b) * (X - C c))) =
        algebraMap k (AdjoinRoot ((X - C a) * (X - C b) * (X - C c)) ⧸ q.asIdeal) b ∨
      Ideal.Quotient.mk q.asIdeal (root ((X - C a) * (X - C b) * (X - C c))) =
        algebraMap k (AdjoinRoot ((X - C a) * (X - C b) * (X - C c)) ⧸ q.asIdeal) c := by
  have h := congrArg (Ideal.Quotient.mk q.asIdeal)
    (eval₂_root ((X - C a) * (X - C b) * (X - C c)))
  simp only [eval₂_mul, eval₂_sub, eval₂_X, eval₂_C, map_mul, map_sub, map_zero] at h
  rcases mul_eq_zero.mp h with hab | hc
  · rcases mul_eq_zero.mp hab with ha | hb
    · exact Or.inl (sub_eq_zero.mp ha)
    · exact Or.inr (Or.inl (sub_eq_zero.mp hb))
  · exact Or.inr (Or.inr (sub_eq_zero.mp hc))

/-- The first branch of a product of three linear factors has actual local
self-length one when its scalar differs from the other two scalars. -/
theorem three_linear_first_local_length (a b c : k) (hab : a ≠ b) (hac : a ≠ c)
    (q : MaximalSpectrum (AdjoinRoot ((X - C a) * (X - C b) * (X - C c))))
    (hq : Ideal.Quotient.mk q.asIdeal (root ((X - C a) * (X - C b) * (X - C c))) =
      algebraMap k (AdjoinRoot ((X - C a) * (X - C b) * (X - C c)) ⧸ q.asIdeal) a) :
    Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) = 1 := by
  apply simple_factor_local_length a (mul_assoc _ _ _) q hq
  simpa only [eval_mul, eval_sub, eval_X, eval_C] using
    mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hac)

end AdjoinRoot
