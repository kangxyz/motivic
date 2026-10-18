/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.CoprimeScalarExtensionIntegral
public import Motivic.Aglib.RingTheory.FiniteExtensionPrimeDegrees
public import Motivic.Aglib.RingTheory.FiniteExtensionPolynomialAvoidance
public import Mathlib.Algebra.Field.ULift

/-!
# Two large scalar extensions retaining the whole closed mark and an actual parameter

Two distinct prime degrees avoid both the residue degree and a prescribed
polynomial degree bound. Each entire scalar-extended affine scheme remains
integral, its whole original closed fiber is a singleton, and its parameter
space has a point in the prescribed principal open. Universe lifting changes
neither extension degree nor cardinality. Both extensions remain finite.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.TensorProduct

universe u

/-- Actual large coprime scalar extensions, including the full closed-point
fiber and a parameter avoiding the unchanged original polynomial condition. -/
theorem exists_two_large_prime_scalar_extensions
    (k R : Type u) [Field k] [Finite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (x : PrimeSpectrum R) [x.asIdeal.IsMaximal]
    {σ : Type u} [Finite σ] (q : MvPolynomial σ k) (hq : q ≠ 0) (N : ℕ) :
    ∃ n m : ℕ, n.Prime ∧ m.Prime ∧ N < n ∧ N < m ∧ n ≠ m ∧ n.Coprime m ∧
      ∀ (r : ℕ) [NeZero r], r = n ∨ r = m →
        let L := ULift.{u} (FiniteField.Extension k p r)
        Module.finrank k L = r ∧ IsDomain (R ⊗[k] L) ∧
          (∃! y : PrimeSpectrum (R ⊗[k] L),
            PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x) ∧
          ∃ c : σ → L, MvPolynomial.eval₂ (algebraMap k L) c q ≠ 0 := by
  let := QuadraticIncidence.ClosedPoint.residueField_finite k R x
  obtain ⟨n, m, hn, hm, hNn, hNm, hne, hen, hem, hnm⟩ :=
    Nat.exists_two_large_prime_degrees_coprime
      (Module.finrank k x.asIdeal.ResidueField) (max N q.totalDegree)
      Module.finrank_pos.ne'
  refine ⟨n, m, hn, hm, (le_max_left _ _).trans_lt hNn,
    (le_max_left _ _).trans_lt hNm, hne, hnm, ?_⟩
  intro r _ hr
  let L := ULift.{u} (FiniteField.Extension k p r)
  have hdegree : Module.finrank k L = r :=
    (ULift.moduleEquiv (R := k) (M := FiniteField.Extension k p r)).finrank_eq.trans
      (FiniteField.finrank_extension k p r)
  have her : (Module.finrank k x.asIdeal.ResidueField).Coprime r := by
    rcases hr with rfl | rfl
    · exact hen
    · exact hem
  have hqr : q.totalDegree < r := by
    rcases hr with rfl | rfl
    · exact (le_max_right _ _).trans_lt hNn
    · exact (le_max_right _ _).trans_lt hNm
  obtain ⟨hD, hunique⟩ := isDomain_and_unique_prime_over_of_coprime_closedPoint k R L x
    (hdegree.symm ▸ her)
  refine ⟨hdegree, hD, hunique, ?_⟩
  apply MvPolynomial.exists_eval₂_ne_zero_of_totalDegree_lt_card q hq
  have hcard : Nat.card L = Nat.card k ^ r := by
    simpa only [L, Nat.card_ulift] using FiniteField.natCard_extension k p r
  rw [hcard]
  exact hqr.trans (Nat.lt_pow_self Finite.one_lt_card)

end Algebra.TensorProduct
