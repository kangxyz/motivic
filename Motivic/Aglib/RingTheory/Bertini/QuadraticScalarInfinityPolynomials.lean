/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.QuadraticScalarClosedInfinityAvoidance

/-! # Original infinity polynomials valid after every scalar extension

The polynomials are constructed over the original field before any extension
or parameter tuple is chosen. The closed polynomial is the product over the
minimal primes of the original, possibly nonreduced ideal.
-/

@[expose] public noncomputable section

open _root_.MvPolynomial

universe u

namespace QuadraticIncidence.InfinityChart

/-- Common original chart relations for an arbitrary number of rows. For zero
rows the relation is `1`, in the actual trivial boundary incidence algebra. -/
theorem exists_nonzero_common_boundary_relation
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    {σ : Type u} [Finite σ] (g : σ → R) (n : ℕ)
    (hn : Algebra.trdeg k R ≤ (n : Cardinal.{u})) :
    ∃ q : MvPolynomial (Fin n × Exponent σ) k, q ≠ 0 ∧
      ∀ j : Exponent σ, monomialFunction k R g j ≠ 0 →
        ProjectiveEvaluationIncidence.parameterMap (boundaryRing k R g j) k
          (boundaryCoordinate k R g j) n q = 0 := by
  cases n with
  | zero =>
      refine ⟨1, one_ne_zero, ?_⟩
      intro j hj
      let : Subsingleton (boundaryRing k R g j) :=
        boundaryRing_subsingleton_of_trdeg_zero k R g j hj (by simpa using hn)
      exact Subsingleton.elim _ _
  | succ n =>
      exact exists_nonzero_common_infinity_relation k R g n (by simpa using hn)

/-- A single original product controls every minimal component after every
actual scalar extension satisfying going down. The extended ideal is unchanged. -/
theorem exists_scalar_closed_infinity_polynomial
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (hI : I ≠ ⊥)
    {σ : Type u} [Finite σ] (g : σ → R) (d : ℕ)
    (hd : Algebra.trdeg k R ≤ (d : Cardinal.{u}) + 1) :
    ∃ Q : MvPolynomial (Fin d × Exponent σ) k, Q ≠ 0 ∧
      ∀ (L S : Type u) [Field L] [CommRing S]
        [Algebra k L] [Algebra L S] [Algebra k S] [IsScalarTower k L S]
        [Algebra R S] [IsScalarTower k R S] [Algebra.HasGoingDown R S]
        (c : Fin d × Exponent σ → L),
        eval₂ (algebraMap k L) c Q ≠ 0 →
        NoCommonClosedInfinityZero L S (I.map (algebraMap R S))
          (algebraMap R S ∘ g) d c := by
  classical
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let : Fintype I.minimalPrimes := I.finite_minimalPrimes_of_isNoetherianRing.fintype
  let : ∀ P : I.minimalPrimes, P.val.IsPrime := fun P => P.property.isPrime
  have hP (P : I.minimalPrimes) : P.val ≠ ⊥ := by
    intro hp
    exact hI (le_bot_iff.mp (hp ▸ P.property.le))
  choose q hq hrel using fun P : I.minimalPrimes =>
    exists_nonzero_common_boundary_relation k (R ⧸ P.val)
      (Ideal.Quotient.mk P.val ∘ g) d (P.val.trdeg_quotient_le_of_ne_bot (hP P) hd)
  refine ⟨∏ P, q P, Finset.prod_ne_zero_iff.mpr (fun P _ => hq P), ?_⟩
  intro L S _ _ _ _ _ _ _ _ _ c hc
  apply noCommonClosedInfinityZero_of_original_eval₂_relations k L R S I g d q hrel c
  intro P
  rw [eval₂_prod] at hc
  exact Finset.prod_ne_zero_iff.mp hc P (Finset.mem_univ P)

/-- Original ambient and closed polynomials, with a simultaneous universal
actual-scalar consumer. No parameter choice, infinite field, further extension,
or reduced replacement of the original ideal is an input. -/
theorem exists_scalar_infinity_polynomials
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (hI : I ≠ ⊥)
    {σ : Type u} [Finite σ] (g : σ → R) (d : ℕ)
    (hd : Algebra.trdeg k R ≤ (d : Cardinal.{u}) + 1) :
    ∃ (F : MvPolynomial (Fin (d + 1) × Exponent σ) k)
      (Q : MvPolynomial (Fin d × Exponent σ) k), F ≠ 0 ∧ Q ≠ 0 ∧
      ∀ (L S : Type u) [Field L] [CommRing S] [IsDomain S]
        [Algebra k L] [Algebra L S] [Algebra k S] [IsScalarTower k L S]
        [Algebra R S] [IsScalarTower k R S] [Algebra.HasGoingDown R S],
        Function.Injective (algebraMap R S) →
        ∀ (z : Fin (d + 1) × Exponent σ → L) (c : Fin d × Exponent σ → L),
        eval₂ (algebraMap k L) z F ≠ 0 → eval₂ (algebraMap k L) c Q ≠ 0 →
        NoCommonInfinityZero L S (algebraMap R S ∘ g) d z ∧
        NoCommonClosedInfinityZero L S (I.map (algebraMap R S))
          (algebraMap R S ∘ g) d c := by
  obtain ⟨F, hF, hrel⟩ := exists_nonzero_common_infinity_relation k R g d hd
  obtain ⟨Q, hQ, hclosed⟩ := exists_scalar_closed_infinity_polynomial k R I hI g d hd
  refine ⟨F, Q, hF, hQ, ?_⟩
  intro L S _ _ _ _ _ _ _ _ _ _ hf z c hz hc
  constructor
  · exact noCommonInfinityZero_of_original_eval₂_relation k L R S
      (IsScalarTower.toAlgHom k R S) hf g d F hrel z hz
  · exact hclosed L S c hc

end QuadraticIncidence.InfinityChart
