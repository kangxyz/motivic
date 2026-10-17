/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.AdjoinRootFactorLength
public import Lean.Util.CollectAxioms

/-!
# Repeated-factor consumers of original quotient local lengths

These consumers retain arbitrary positive powers of an irreducible factor,
including an arbitrary complementary factor that is invertible at that branch.
They use the original quotient localization, rather than its reduced quotient.
-/

@[expose] public noncomputable section

open Polynomial AdjoinRoot UniqueFactorizationMonoid

namespace Motivic.MotivicTest.AdjoinRootFactorLength

variable {k : Type*} [Field k]

/-- The original branch in an arbitrary nonzero power of a monic irreducible. -/
def powerBranch (q : {q : k[X] // q.Monic ∧ Irreducible q}) (n : ℕ) (hn : n ≠ 0) :
    IrreducibleBranch (q.val ^ n) :=
  ⟨q, dvd_pow_self _ hn⟩

/-- Arbitrarily large repeated-factor lengths survive in the original local ring. -/
theorem repeated_factor_length (q : {q : k[X] // q.Monic ∧ Irreducible q})
    (n : ℕ) (hn : n ≠ 0) :
    Module.length
      (Localization.AtPrime (branchMaximal (q.val ^ n) (powerBranch q n hn)).asIdeal)
      (Localization.AtPrime (branchMaximal (q.val ^ n) (powerBranch q n hn)).asIdeal) = n := by
  rw [branch_local_length_eq_emultiplicity _ (pow_ne_zero _ q.property.2.ne_zero)]
  exact emultiplicity_pow_self q.property.2.ne_zero q.property.2.not_isUnit n

/-- The actual branch of a repeated factor times an arbitrary complement. -/
def powerTimesBranch (q : {q : k[X] // q.Monic ∧ Irreducible q})
    (n : ℕ) (hn : n ≠ 0) (g : k[X]) : IrreducibleBranch (q.val ^ n * g) :=
  ⟨q, dvd_mul_of_dvd_left (dvd_pow_self _ hn) _⟩

/-- A complementary polynomial cannot change the local multiplicity when the
chosen irreducible does not divide it. The complement may have repeated factors. -/
theorem repeated_factor_with_complement_length
    (q : {q : k[X] // q.Monic ∧ Irreducible q}) (n : ℕ) (hn : n ≠ 0)
    (g : k[X]) (hqg : ¬q.val ∣ g) :
    Module.length
      (Localization.AtPrime
        (branchMaximal (q.val ^ n * g) (powerTimesBranch q n hn g)).asIdeal)
      (Localization.AtPrime
        (branchMaximal (q.val ^ n * g) (powerTimesBranch q n hn g)).asIdeal) = n := by
  have hg : g ≠ 0 := by
    intro h
    exact hqg (h ▸ dvd_zero _)
  rw [branch_local_length_eq_emultiplicity _ (mul_ne_zero
    (pow_ne_zero _ q.property.2.ne_zero) hg)]
  change emultiplicity q.val (q.val ^ n * g) = n
  rw [emultiplicity_mul q.property.2.prime,
    emultiplicity_pow_self q.property.2.ne_zero q.property.2.not_isUnit,
    emultiplicity_eq_zero.mpr hqg, add_zero]

open scoped Classical in
/-- Passing to the natural coefficient loses no finite multiplicity. -/
theorem original_local_coefficient_eq_factor_count (p : k[X]) (hp : p.Monic)
    (q : IrreducibleBranch p) :
    (Module.length (Localization.AtPrime (branchMaximal p q).asIdeal)
      (Localization.AtPrime (branchMaximal p q).asIdeal)).toNat =
        (normalizedFactors p).count q.val.val := by
  rw [branch_local_length_eq_count_normalizedFactors p hp q, ENat.toNat_natCast]

open Lean in
run_cmd do
  for name in #[``AdjoinRoot.branchLocalizationQuotientEquiv,
      ``AdjoinRoot.factorLocalRing_map_span,
      ``AdjoinRoot.branch_local_length_eq_multiplicity,
      ``AdjoinRoot.branch_local_length_eq_emultiplicity,
      ``AdjoinRoot.branch_local_length_eq_count_normalizedFactors,
      ``repeated_factor_length, ``repeated_factor_with_complement_length,
      ``original_local_coefficient_eq_factor_count] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Repeated-factor local lengths use only standard Lean foundations."

end Motivic.MotivicTest.AdjoinRootFactorLength
