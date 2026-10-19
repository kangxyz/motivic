/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticInfinityAvoidance
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.FiniteType

/-! # One same-family polynomial avoids all actual minimal-component infinity charts

Only a statement about the actual component support is made here. The original
possibly nonreduced closed subscheme is not replaced by its reduction.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.MvPolynomial
universe u
namespace QuadraticIncidence.InfinityChart

/-- In transcendence degree zero the actual chart infinity coordinate is a unit,
so its full quotient ring is trivial, not merely devoid of rational points. -/
theorem boundaryRing_subsingleton_of_trdeg_zero
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    {σ : Type u} (g : σ → R) (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) (hd : Algebra.trdeg k R ≤ 0) :
    Subsingleton (boundaryRing k R g j) := by
  have he : Algebra.trdeg k (chart k R g j) = 0 :=
    le_antisymm ((trdeg_chart_le k R g j).trans hd) zero_le
  let : Algebra.IsAlgebraic k (chart k R g j) := trdeg_eq_zero_iff.mp he
  have hu : IsUnit (infinityCoordinate k R g j) :=
    (Algebra.IsIntegral.isIntegral (R := k) (infinityCoordinate k R g j)).isUnit
      (infinityCoordinate_ne_zero k R g j hj)
  exact (Ideal.Quotient.subsingleton_iff).mpr (Ideal.span_singleton_eq_top.mpr hu)

/-- The arbitrary number of original forms includes zero: in that case the
actual infinity charts are trivial. No `d > 0` premise survives. -/
theorem exists_infinity_avoidance_polynomial_of_trdeg_le
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    {σ : Type u} [Finite σ] (g : σ → R) (d : ℕ)
    (hd : Algebra.trdeg k R ≤ (d : Cardinal.{u})) :
    ∃ q : MvPolynomial (Fin d × Exponent σ) k, q ≠ 0 ∧
      ∀ c, eval c q ≠ 0 → ∀ j : Exponent σ, monomialFunction k R g j ≠ 0 →
        ∀ (K : Type u) [Field K] [Algebra k K] [Algebra (boundaryRing k R g j) K]
          [IsScalarTower k (boundaryRing k R g j) K],
          ¬ ProjectiveEvaluationIncidence.Vanishes k (boundaryRing k R g j) K
            (boundaryCoordinate k R g j) d c := by
  cases d with
  | zero =>
      refine ⟨1, one_ne_zero, ?_⟩
      intro c hc j hj K hK hkK hAK ht hzero
      let : Subsingleton (boundaryRing k R g j) :=
        boundaryRing_subsingleton_of_trdeg_zero k R g j hj (by simpa using hd)
      let z := hAK.algebraMap
      have hz : z 0 = z 1 := congrArg (fun a : boundaryRing k R g j => z a)
        (Subsingleton.elim 0 1)
      exact zero_ne_one (by simpa only [map_zero, map_one] using hz)
  | succ d =>
      exact exists_infinity_avoidance_polynomial k R g d (by simpa using hd)

/-- All minimal-prime components are those of the original ideal. Their equations
and quadratic parameter indices are unchanged. -/
def NoCommonClosedInfinityZero
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (I : Ideal R) {σ : Type u} [Finite σ] (g : σ → R) (d : ℕ)
    (c : Fin d × Exponent σ → k) : Prop :=
  ∀ P : I.minimalPrimes, letI : P.val.IsPrime := P.property.isPrime
    ∀ j : Exponent σ, monomialFunction k (R ⧸ P.val) (Ideal.Quotient.mk P.val ∘ g) j ≠ 0 →
      ∀ (K : Type u) [Field K] [Algebra k K]
        [Algebra (boundaryRing k (R ⧸ P.val) (Ideal.Quotient.mk P.val ∘ g) j) K]
        [IsScalarTower k (boundaryRing k (R ⧸ P.val) (Ideal.Quotient.mk P.val ∘ g) j) K],
        ¬ ProjectiveEvaluationIncidence.Vanishes k
          (boundaryRing k (R ⧸ P.val) (Ideal.Quotient.mk P.val ∘ g) j) K
          (boundaryCoordinate k (R ⧸ P.val) (Ideal.Quotient.mk P.val ∘ g) j) d c

/-- One nonzero ground polynomial controls all actual finite minimal components.
This is support avoidance, not an assertion of finiteness on a reduced substitute. -/
theorem exists_closed_infinity_avoidance_polynomial
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (hI : I ≠ ⊥)
    {σ : Type u} [Finite σ] (g : σ → R) (d : ℕ)
    (hd : Algebra.trdeg k R ≤ (d : Cardinal.{u}) + 1) :
    ∃ q : MvPolynomial (Fin d × Exponent σ) k, q ≠ 0 ∧
      ∀ c, eval c q ≠ 0 → NoCommonClosedInfinityZero k R I g d c := by
  classical
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let : Fintype I.minimalPrimes := I.finite_minimalPrimes_of_isNoetherianRing.fintype
  let : ∀ P : I.minimalPrimes, P.val.IsPrime := fun P => P.property.isPrime
  have hP (P : I.minimalPrimes) : P.val ≠ ⊥ := by
    intro hp
    exact hI (le_bot_iff.mp (hp ▸ P.property.le))
  choose q hq hgood using fun P : I.minimalPrimes =>
    exists_infinity_avoidance_polynomial_of_trdeg_le k (R ⧸ P.val)
      (Ideal.Quotient.mk P.val ∘ g) d (P.val.trdeg_quotient_le_of_ne_bot (hP P) hd)
  refine ⟨∏ P, q P, Finset.prod_ne_zero_iff.mpr (fun P _ => hq P), ?_⟩
  intro c hc P
  apply hgood P c
  rw [map_prod] at hc
  exact Finset.prod_ne_zero_iff.mp hc P (Finset.mem_univ P)

end QuadraticIncidence.InfinityChart
