/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.SteinbergTorsion
public import Motivic.Cohomology.WeightTwo.SplitPolynomialCycle
public import Motivic.Cohomology.WeightTwo.SkewSymmetry
public import Motivic.Cohomology.WeightTwo.CorestrictionDegree
public import Motivic.Aglib.RingTheory.AdjoinRoot.BranchDimension

/-!
# A uniform annihilator and the genuine weight-two Steinberg relation

The literal cubic boundary, with all three factors at both ends retained,
first bounds complementary symbols over a field containing a cubic root of
unity. Whole finite polynomial algebras descend this bound with their actual
residue degrees and local lengths. The previously proved torsion-removal
argument then gives the integral Steinberg relation on the original raw H22.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
open Polynomial.TwoUnitPolynomialFamily
open scoped BigOperators TensorProduct

universe u

namespace Motivic.WeightTwoSteinbergBound

open WeightTwoSymbols WeightTwoSteinbergTorsion WeightTwoSkewSymmetry
open WeightTwoCubicBoundary WeightTwoSplitPolynomialCycle WeightTwoCorestriction
open WeightTwoPolynomialTransfer

variable {k : Type u} [Field k]

local instance quotientField {R : Type u} [CommRing R] (q : MaximalSpectrum R) :
    Field (R ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal

/-- The quadratic relation gives the exact cubic power, without choosing a root field. -/
theorem cube_eq_one_of_quadratic (w : k) (hw : w ^ 2 + w + 1 = 0) : w ^ 3 = 1 := by
  linear_combination (w - 1) * hw

/-- The three complementary factors retain their literal product. -/
theorem complement_product (w a : k) (hw : w ^ 2 + w + 1 = 0) :
    (1 - a) * (1 - w * a) * (1 - w ^ 2 * a) = 1 - a ^ 3 := by
  have hw3 := cube_eq_one_of_quadratic w hw
  linear_combination (a ^ 2 - a) * hw + (a ^ 2 - a ^ 3) * hw3

/-- The zero endpoint splits into the three original scalar factors. -/
theorem cubicZero_factorization (w a : k) (hw : w ^ 2 + w + 1 = 0) :
    cubicZero a = (X - C a) * (X - C (w * a)) * (X - C (w ^ 2 * a)) := by
  have hw3 := cube_eq_one_of_quadratic w hw
  have hC := congrArg (C : k →+* k[X]) hw
  have hC3 := congrArg (C : k →+* k[X]) hw3
  simp only [map_add, map_pow, map_one, map_zero] at hC hC3
  simp only [cubicZero, map_mul, map_pow]
  linear_combination (C a * X ^ 2 - C a ^ 2 * X) * hC +
    (C a ^ 3 - C a ^ 2 * X) * hC3

/-- The other endpoint retains both quadratic roots, including collisions. -/
theorem cubicOne_factorization (w a : k) (hw : w ^ 2 + w + 1 = 0) :
    cubicOne a = (X - C (a ^ 3)) * (X - C (-w)) * (X - C (-(w ^ 2))) := by
  have hw3 := cube_eq_one_of_quadratic w hw
  have hC := congrArg (C : k →+* k[X]) hw
  have hC3 := congrArg (C : k →+* k[X]) hw3
  simp only [map_add, map_pow, map_one, map_zero] at hC hC3
  simp only [cubicOne, map_neg, map_pow]
  linear_combination -(X - C a ^ 3) * X * hC - (X - C a ^ 3) * hC3

/-- The literal cubic endpoints give the three complementary symbols; the two
quadratic factors cancel by the already established geometric skew symmetry. -/
theorem cubic_symbol_relation (w a b₀ b₁ b₂ c : kˣ)
    (hw : (w : k) ^ 2 + (w : k) + 1 = 0)
    (hb₀ : (b₀ : k) = 1 - (a : k))
    (hb₁ : (b₁ : k) = 1 - (w * a : kˣ))
    (hb₂ : (b₂ : k) = 1 - (w ^ 2 * a : kˣ))
    (hc : (c : k) = 1 - (a : k) ^ 3) :
    graphSymbol k a b₀ + graphSymbol k (w * a) b₁ +
      graphSymbol k (w ^ 2 * a) b₂ = graphSymbol k (a ^ 3) c := by
  have ha3 : (a : k) ^ 3 ≠ 1 := by
    intro h
    apply c.ne_zero
    rw [hc, h, sub_self]
  have h := cubic_cycleClass_endpoints (a : k) a.ne_zero ha3
  unfold zeroCycle oneCycle at h
  rw [cycleClass_eq_three_graphSymbol_of_factorization _ _ _ _ a b₀ (w * a) b₁
    (w ^ 2 * a) b₂ (cubicZero_factorization (w : k) (a : k) hw) hb₀ hb₁ hb₂] at h
  have hneg₁ : (-(w ^ 2) : kˣ) = 1 - ((-w : kˣ) : k) := by
    simp only [Units.val_neg, Units.val_pow_eq_pow_val]
    linear_combination -hw
  have hneg₂ : ((-w : kˣ) : k) = 1 - ((-(w ^ 2) : kˣ) : k) := by
    simp only [Units.val_neg, Units.val_pow_eq_pow_val]
    linear_combination -hw
  rw [cycleClass_eq_three_graphSymbol_of_factorization _ _ _ _ (a ^ 3) c (-w)
    (-(w ^ 2)) (-(w ^ 2)) (-w)
    (cubicOne_factorization (w : k) (a : k) hw) hc hneg₁ hneg₂] at h
  simpa only [add_assoc, graphSymbol_add_swap, add_zero] using h

/-- Over a field with a root of `X²+X+1`, every complementary cube symbol is
annihilated by two, in the original integral raw homology. -/
theorem two_nsmul_cube_symbol (w a c : kˣ)
    (hw : (w : k) ^ 2 + (w : k) + 1 = 0)
    (hc : (c : k) = 1 - (a : k) ^ 3) :
    2 • graphSymbol k (a ^ 3) c = 0 := by
  have hprod := complement_product (w : k) (a : k) hw
  have hp : (1 - (a : k)) * (1 - (w : k) * (a : k)) *
      (1 - (w : k) ^ 2 * (a : k)) ≠ 0 := by
    rw [hprod, ← hc]
    exact c.ne_zero
  obtain ⟨⟨h₀, h₁⟩, h₂⟩ := (mul_ne_zero_iff.mp hp).imp_left mul_ne_zero_iff.mp
  let b₀ : kˣ := Units.mk0 _ h₀
  let b₁ : kˣ := Units.mk0 _ h₁
  let b₂ : kˣ := Units.mk0 _ h₂
  have h := cubic_symbol_relation w a b₀ b₁ b₂ c hw rfl rfl rfl hc
  have hw3 : w ^ 3 = 1 := Units.ext (cube_eq_one_of_quadratic (w : k) hw)
  have hwa : (w * a) ^ 3 = a ^ 3 := by rw [mul_pow, hw3, one_mul]
  have hw2a : (w ^ 2 * a) ^ 3 = a ^ 3 := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm 2 3, pow_mul, hw3, one_pow, one_mul]
  have hb : b₀ * b₁ * b₂ = c := by
    apply Units.ext
    exact hprod.trans hc.symm
  have hscaled := congrArg (fun x => (3 : ℕ) • x) h
  rw [smul_add, smul_add, ← graphSymbol_pow_left, ← graphSymbol_pow_left,
    ← graphSymbol_pow_left, hwa, hw2a, ← graphSymbol_mul_right,
    ← graphSymbol_mul_right, hb] at hscaled
  have he : graphSymbol k (a ^ 3) c + 2 • graphSymbol k (a ^ 3) c =
      graphSymbol k (a ^ 3) c + 0 := by
    simpa only [show 3 = 2 + 1 from rfl, succ_nsmul, add_zero, zero_add, zero_smul,
      add_comm] using hscaled.symm
  exact add_left_cancel he

/-- A bound on every original maximal quotient descends using their true
residue degrees and their original local lengths, totaling the whole degree. -/
theorem polynomial_annihilator_descent (p : k[X]) (hp : p.Monic) (n : ℕ)
    (a b : kˣ)
    (h : ∀ q : MaximalSpectrum (AdjoinRoot p),
      n • graphSymbol (AdjoinRoot p ⧸ q.asIdeal)
        (Units.map (algebraMap k (AdjoinRoot p ⧸ q.asIdeal)).toMonoidHom a)
        (Units.map (algebraMap k (AdjoinRoot p ⧸ q.asIdeal)).toMonoidHom b) = 0) :
    (n * p.natDegree) • graphSymbol k a b = 0 := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  have hbranch (q : MaximalSpectrum (AdjoinRoot p)) :
      n • (Module.finrank k (AdjoinRoot p ⧸ q.asIdeal) • graphSymbol k a b) = 0 := by
    have ht := congrArg (corestriction (k := k)) (h q)
    rw [map_nsmul, ← WeightTwoFieldChange.graphSymbol_fieldChange,
      corestriction_fieldChange, map_zero] at ht
    simpa only [natCast_zsmul] using ht
  rw [← AdjoinRoot.sum_local_length_mul_finrank_eq_natDegree p hp,
    mul_smul, Finset.sum_smul, Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro q _
  rw [mul_smul, smul_comm n, hbranch q, smul_zero]

/-- The whole cubic root algebra descends the cube bound to six over any
field containing a root of the exact quadratic relation. -/
theorem six_nsmul_symbol_of_quadratic_root (w a b : kˣ)
    (hw : (w : k) ^ 2 + (w : k) + 1 = 0)
    (hab : (b : k) = 1 - (a : k)) : 6 • graphSymbol k a b = 0 := by
  let P : k[X] := X ^ 3 - C (a : k)
  have hP : P.Monic := monic_X_pow_sub_C _ (by decide)
  have h0 : IsUnit (P.eval 0) := by
    simpa only [P, eval_sub, eval_pow, eval_X, eval_C, zero_pow (by decide : 3 ≠ 0),
      zero_sub] using a.isUnit.neg
  have hroot : (AdjoinRoot.root P) ^ 3 = AdjoinRoot.of P (a : k) := by
    have hr := AdjoinRoot.eval₂_root P
    simpa only [P, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] using hr
  have hd : P.natDegree = 3 := by
    dsimp only [P]
    compute_degree
    norm_num
  have h := polynomial_annihilator_descent P hP 2 a b (fun q => ?_)
  · simpa only [hd] using h
  let E := AdjoinRoot P ⧸ q.asIdeal
  let φ := algebraMap k E
  have hwE : (Units.map φ.toMonoidHom w : E) ^ 2 +
      (Units.map φ.toMonoidHom w : E) + 1 = 0 := by
    change φ (w : k) ^ 2 + φ (w : k) + 1 = 0
    simpa only [map_add, map_pow, map_one, map_zero] using congrArg φ hw
  have hpow : (residueRootUnit P h0 q) ^ 3 = Units.map φ.toMonoidHom a := by
    apply Units.ext
    change (Ideal.Quotient.mk q.asIdeal (rootUnit P h0)) ^ 3 = φ (a : k)
    rw [rootUnit_val, ← map_pow, hroot]
    rfl
  have hc : (Units.map φ.toMonoidHom b : E) =
      1 - (residueRootUnit P h0 q : E) ^ 3 := by
    change φ (b : k) = 1 - (residueRootUnit P h0 q : E) ^ 3
    rw [← Units.val_pow_eq_pow_val, hpow]
    change φ (b : k) = 1 - φ (a : k)
    rw [hab, map_sub, map_one]
  have he := two_nsmul_cube_symbol (Units.map φ.toMonoidHom w)
    (residueRootUnit P h0 q) (Units.map φ.toMonoidHom b) hwE hc
  simpa only [hpow] using he

/-- Twelve is an actual universal positive bound for complementary graph
symbols. The quadratic quotient contributes all of its true degree two. -/
theorem twelve_nsmul_graphSymbol (a b : kˣ)
    (hab : (b : k) = 1 - (a : k)) : 12 • graphSymbol k a b = 0 := by
  let P : k[X] := X ^ 2 + X + 1
  have hP : P.Monic := by dsimp only [P]; monicity; norm_num
  have h0 : IsUnit (P.eval 0) := by simp only [P, eval_add, eval_pow, eval_X,
    eval_one, zero_pow (by decide : 2 ≠ 0), zero_add]; exact isUnit_one
  have hd : P.natDegree = 2 := by dsimp only [P]; compute_degree; norm_num
  have hroot : (AdjoinRoot.root P) ^ 2 + AdjoinRoot.root P + 1 = 0 := by
    have hr := AdjoinRoot.eval₂_root P
    simpa only [P, eval₂_add, eval₂_pow, eval₂_X, eval₂_one] using hr
  have h := polynomial_annihilator_descent P hP 6 a b (fun q => ?_)
  · simpa only [hd] using h
  let E := AdjoinRoot P ⧸ q.asIdeal
  let φ := algebraMap k E
  let w := residueRootUnit P h0 q
  have hw : (w : E) ^ 2 + (w : E) + 1 = 0 := by
    have he := congrArg (Ideal.Quotient.mk q.asIdeal) hroot
    change Ideal.Quotient.mk q.asIdeal (rootUnit P h0) ^ 2 +
      Ideal.Quotient.mk q.asIdeal (rootUnit P h0) + 1 = 0
    rw [rootUnit_val]
    simpa only [map_add, map_pow, map_one, map_zero] using he
  apply six_nsmul_symbol_of_quadratic_root w _ _ hw
  change φ (b : k) = 1 - φ (a : k)
  rw [hab, map_sub, map_one]

/-- Existence is established for the previously defined universal bound predicate. -/
theorem universalSteinbergAnnihilator_twelve : UniversalSteinbergAnnihilator.{u} 12 := by
  intro F _ _ a b hab
  exact twelve_nsmul_graphSymbol a b hab

/-- The Steinberg relation holds on the original graph symbols over every
characteristic-zero field, with no remaining comparison or torsion hypothesis. -/
theorem graphSymbol_steinberg [CharZero k] (a b : kˣ)
    (hab : (b : k) = 1 - (a : k)) : graphSymbol k a b = 0 :=
  graphSymbol_eq_zero_of_universal_annihilator 12 (by decide)
    universalSteinbergAnnihilator_twelve k a b hab

end Motivic.WeightTwoSteinbergBound
