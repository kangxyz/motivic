/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.AdjoinRootBranchDimension
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Tactic.FinCases
public import Lean.Util.CollectAxioms

/-!
# Consumers of the whole polynomial-quotient branch dimension

The concrete quadratic over the field with three elements has residue degree
two. Arbitrarily repeated linear factors retain their full degree, without
replacing the original quotient by its reduction. The axiom audit rejects all
assumptions outside the standard Lean foundations.
-/

@[expose] public noncomputable section

open Polynomial
open scoped BigOperators

namespace Motivic.MotivicTest.AdjoinRootBranchDimension

universe u

/-- A concrete nonsplit quadratic over the field with three elements. -/
def nonsplit : (ZMod 3)[X] := X ^ 2 + C 1

/-- The concrete nonsplit polynomial is monic. -/
theorem nonsplit_monic : nonsplit.Monic :=
  monic_X_pow_add_C 1 (by decide)

/-- Its literal quotient has dimension two. -/
theorem nonsplit_natDegree : nonsplit.natDegree = 2 :=
  natDegree_X_pow_add_C

/-- None of the three base-field elements is a root. -/
theorem nonsplit_irreducible : Irreducible nonsplit := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp only [nonsplit_natDegree, Finset.mem_Icc]
    decide
  · intro x
    simp only [IsRoot, nonsplit, eval_add, eval_pow, eval_X, eval_C]
    fin_cases x <;> decide

local instance : Fact (Irreducible nonsplit) := ⟨nonsplit_irreducible⟩

/-- The actual closed point of the nonsplit quadratic quotient. -/
def nonsplitBranch : MaximalSpectrum (AdjoinRoot nonsplit) :=
  ⟨⊥, Ideal.bot_isMaximal⟩

/-- The residue degree is genuinely two, so scalar-root branch formulas do
not apply to this example. -/
theorem nonsplit_residue_degree :
    Module.finrank (ZMod 3) (AdjoinRoot nonsplit ⧸ nonsplitBranch.asIdeal) = 2 := by
  calc
    _ = Module.finrank (ZMod 3) (AdjoinRoot nonsplit) :=
      (AlgEquiv.quotientBot (ZMod 3) (AdjoinRoot nonsplit)).toLinearEquiv.finrank_eq
    _ = nonsplit.natDegree := finrank_quotient_span_eq_natDegree
    _ = 2 := nonsplit_natDegree

/-- The full branch sum includes the nontrivial residue extension. -/
theorem nonsplit_whole_quotient_dimension :
    letI := nonsplit_monic.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot nonsplit) := .of_finite (ZMod 3) _
    letI : Fintype (MaximalSpectrum (AdjoinRoot nonsplit)) := Fintype.ofFinite _
    ∑ q : MaximalSpectrum (AdjoinRoot nonsplit),
      (Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat *
          Module.finrank (ZMod 3) (AdjoinRoot nonsplit ⧸ q.asIdeal) = 2 := by
  exact (AdjoinRoot.sum_local_length_mul_finrank_eq_natDegree nonsplit
    nonsplit_monic).trans nonsplit_natDegree

/-- Arbitrary repeated roots keep every original local multiplicity, in
all characteristics and including the empty degree-zero case. -/
theorem repeated_root_dimension {k : Type u} [Field k] (a : k) (m : ℕ) :
    letI := ((monic_X_sub_C a).pow m).finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot ((X - C a) ^ m)) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot ((X - C a) ^ m))) := Fintype.ofFinite _
    ∑ q : MaximalSpectrum (AdjoinRoot ((X - C a) ^ m)),
      (Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat *
          Module.finrank k (AdjoinRoot ((X - C a) ^ m) ⧸ q.asIdeal) = m := by
  simpa only [natDegree_pow, natDegree_X_sub_C, mul_one] using
    AdjoinRoot.sum_local_length_mul_finrank_eq_natDegree ((X - C a) ^ m)
      ((monic_X_sub_C a).pow m)

open Lean in
run_cmd do
  for name in #[``Algebra.finrank_eq_sum_local_length_mul_finrank,
      ``AdjoinRoot.sum_local_length_mul_finrank_eq_natDegree,
      ``nonsplit_monic, ``nonsplit_natDegree, ``nonsplit_irreducible,
      ``nonsplitBranch, ``nonsplit_residue_degree,
      ``nonsplit_whole_quotient_dimension, ``repeated_root_dimension] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole polynomial-quotient branch dimensions use only standard Lean foundations."

end Motivic.MotivicTest.AdjoinRootBranchDimension
