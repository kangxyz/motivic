/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.AdjoinRootSimpleLocalization
public import Motivic.Aglib.RingTheory.MonicUnitInterpolation
public import Mathlib.Algebra.Field.ZMod

/-!
# Consumers of actual simple-root local lengths

The tests retain the original quotient's prime and localization, including a
positive-characteristic example with an arbitrarily repeated other factor.
-/

@[expose] public noncomputable section

open Polynomial Polynomial.MonicUnitInterpolation

namespace Motivic.MotivicTest.AdjoinRootSimpleLocalization

universe u

variable {k : Type u} [Field k]

/-- The local multiplicity is the natural number obtained from the actual
local self-length, with no reduced support replacing the original quotient. -/
theorem simple_branch_multiplicity (a : k) (ha : a ≠ 1) (m : ℕ)
    (q : MaximalSpectrum (AdjoinRoot ((X - 1) ^ m * (X - C a))))
    (hq : Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root ((X - 1) ^ m * (X - C a))) =
      algebraMap k (AdjoinRoot ((X - 1) ^ m * (X - C a)) ⧸ q.asIdeal) a) :
    (Module.length (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal)).toNat = 1 := by
  rw [AdjoinRoot.split_simple_local_length a ha m q hq]
  rfl

/-- The literal monic-interpolation endpoint uses the same simple-branch
length theorem at its determinant-norm coordinate. -/
theorem target_simple_local_length (p : k[X]) (ha : normValue p ≠ 1)
    (q : MaximalSpectrum (AdjoinRoot (target p)))
    (hq : Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root (target p)) =
      algebraMap k (AdjoinRoot (target p) ⧸ q.asIdeal) (normValue p)) :
    Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) = 1 := by
  exact AdjoinRoot.split_simple_local_length (normValue p) ha (p.natDegree - 1) q hq

/-- Characteristic two does not remove repeated identity factors: only the
other, distinct root is asserted to have local length one. -/
theorem characteristic_two_simple_branch (m : ℕ)
    (q : MaximalSpectrum (AdjoinRoot ((X - 1) ^ m * (X - C (0 : ZMod 2)))))
    (hq : Ideal.Quotient.mk q.asIdeal
      (AdjoinRoot.root ((X - 1) ^ m * (X - C (0 : ZMod 2)))) = 0) :
    Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) = 1 := by
  apply AdjoinRoot.split_simple_local_length (0 : ZMod 2) zero_ne_one m q
  simpa only [map_zero] using hq

open Lean in
run_cmd do
  for name in #[``AdjoinRoot.localization_algebraMap_surjective_of_root_eq,
      ``AdjoinRoot.local_length_eq_one_of_root_eq, ``AdjoinRoot.split_simple_local_length,
      ``simple_branch_multiplicity, ``target_simple_local_length,
      ``characteristic_two_simple_branch] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual simple-root localization audit passed: standard foundations only."

end Motivic.MotivicTest.AdjoinRootSimpleLocalization
