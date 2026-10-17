/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.AdjoinRootSimpleFactorLocalization
public import Mathlib.Algebra.Field.ZMod
public import Lean.Util.CollectAxioms

/-!
# Consumers of simple linear factors in the original local ring

The tests retain the original quotient and its localization, including a
characteristic-two cubic whose complementary factors coincide. The audit
checks all new library declarations for standard foundations only.
-/

@[expose] public noncomputable section

open Polynomial

namespace Motivic.MotivicTest.AdjoinRootSimpleFactorLocalization

universe u

variable {k : Type u} [Field k]

/-- Converting the original local length to a natural number preserves the
simple branch's multiplicity, for an arbitrary complementary polynomial. -/
theorem original_simple_factor_multiplicity (a : k) (g : k[X])
    (q : MaximalSpectrum (AdjoinRoot ((X - C a) * g)))
    (hq : Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root ((X - C a) * g)) =
      algebraMap k (AdjoinRoot ((X - C a) * g) ⧸ q.asIdeal) a)
    (hg : g.eval a ≠ 0) :
    (Module.length (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal)).toNat = 1 := by
  rw [AdjoinRoot.simple_factor_local_length a rfl q hq hg]
  rfl

/-- A repeated complementary branch is allowed; only the chosen branch must
be simple in the original cubic. -/
theorem repeated_complement_simple_branch (a b : k) (hab : a ≠ b)
    (q : MaximalSpectrum (AdjoinRoot ((X - C a) * (X - C b) * (X - C b))))
    (hq : Ideal.Quotient.mk q.asIdeal
      (AdjoinRoot.root ((X - C a) * (X - C b) * (X - C b))) =
      algebraMap k (AdjoinRoot ((X - C a) * (X - C b) * (X - C b)) ⧸ q.asIdeal) a) :
    Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) = 1 :=
  AdjoinRoot.three_linear_first_local_length a b b hab hab q hq

/-- Characteristic two does not require the complementary factor to be
reduced or separable in the original quotient. -/
theorem characteristic_two_repeated_complement
    (q : MaximalSpectrum (AdjoinRoot
      ((X - C (0 : ZMod 2)) * (X - C (1 : ZMod 2)) * (X - C (1 : ZMod 2)))))
    (hq : Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root
      ((X - C (0 : ZMod 2)) * (X - C (1 : ZMod 2)) * (X - C (1 : ZMod 2)))) = 0) :
    Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) = 1 := by
  apply repeated_complement_simple_branch (0 : ZMod 2) 1 zero_ne_one q
  simpa only [map_zero] using hq

/-- Degree remains three when all scalar roots collide. -/
theorem triple_collision_degree (a : k) :
    ((X - C a) * (X - C a) * (X - C a)).natDegree = 3 :=
  AdjoinRoot.three_linear_natDegree a a a

open Lean in
run_cmd do
  for name in #[``AdjoinRoot.localization_isUnit_mk_of_residual_root_eq,
      ``AdjoinRoot.localization_root_eq_of_simple_factor,
      ``AdjoinRoot.simple_factor_local_length, ``AdjoinRoot.three_linear_monic,
      ``AdjoinRoot.three_linear_natDegree, ``AdjoinRoot.three_linear_residual_root,
      ``AdjoinRoot.three_linear_first_local_length, ``original_simple_factor_multiplicity,
      ``repeated_complement_simple_branch, ``characteristic_two_repeated_complement,
      ``triple_collision_degree] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Simple-factor localization audit passed: standard foundations only."

end Motivic.MotivicTest.AdjoinRootSimpleFactorLocalization
