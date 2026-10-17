/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoPolynomialTransfer

/-!
# Removing universal Steinberg torsion on the original graph symbols

The hypothesis is a universal annihilator, not a Steinberg relation. For the
whole polynomial `X ^ p - a`, each original maximal quotient has a root `b`
with `b ^ p = a`. Bilinearity, the actual mixed corestriction, and the product
of complement norms with the original local lengths remove the factor `p`.
No chosen root field is assigned degree `p`, and no separability is needed.
Taking `p` to be the entire positive annihilator proves vanishing directly.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
open Polynomial.TwoUnitPolynomialFamily
open scoped BigOperators

universe u

namespace Motivic.WeightTwoSteinbergTorsion

open WeightTwoSymbols WeightTwoPolynomialTransfer WeightTwoCorestriction

variable {k : Type u} [Field k]

local instance quotientField {R : Type u} [CommRing R] (q : MaximalSpectrum R) :
    Field (R ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal

/-- Powers in the left unit give repeated addition of the actual graph class. -/
theorem graphSymbol_pow_left (a b : kˣ) (n : ℕ) :
    graphSymbol k (a ^ n) b = n • graphSymbol k a b := by
  induction n with
  | zero => simp only [pow_zero, graphSymbol_one_left, zero_smul]
  | succ n ih => rw [pow_succ, graphSymbol_mul_left, ih, succ_nsmul]

/-- Powers in the right unit give repeated addition of the actual graph class. -/
theorem graphSymbol_pow_right (a b : kˣ) (n : ℕ) :
    graphSymbol k a (b ^ n) = n • graphSymbol k a b := by
  induction n with
  | zero => simp only [pow_zero, graphSymbol_one_right, zero_smul]
  | succ n ih => rw [pow_succ, graphSymbol_mul_right, ih, succ_nsmul]

/-- Multiplying all branch norms adds their original graph classes. -/
theorem graphSymbol_prod_right {ι : Type*} (s : Finset ι) (a : kˣ) (b : ι → kˣ) :
    graphSymbol k a (∏ i ∈ s, b i) = ∑ i ∈ s, graphSymbol k a (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, graphSymbol_one_right, Finset.sum_empty]
  | @insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi,
      graphSymbol_mul_right, ih]

/-- A universal torsion bound for complementary units in characteristic zero.
This is only a predicate; no existence of such a bound is asserted here. -/
def UniversalSteinbergAnnihilator (n : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (a b : Fˣ),
    (b : F) = 1 - (a : F) → n • graphSymbol F a b = 0

/-- A whole root polynomial removes any positive factor from a universal bound.
All its original residue fields and local lengths enter the norm calculation. -/
theorem remove_positive_factor (m p : ℕ) (hp : 0 < p)
    (h : UniversalSteinbergAnnihilator.{u} (m * p)) :
    UniversalSteinbergAnnihilator.{u} m := by
  classical
  intro F _ _ a b hab
  let P : F[X] := X ^ p - C (a : F)
  have hP : P.Monic := monic_X_pow_sub_C _ hp.ne'
  have h0 : IsUnit (P.eval 0) := by
    simpa only [P, eval_sub, eval_pow, eval_X, eval_C, zero_pow hp.ne', zero_sub]
      using a.isUnit.neg
  have h1 : IsUnit (P.eval 1) := by
    simpa only [P, eval_sub, eval_pow, eval_X, eval_C, one_pow, ← hab]
      using b.isUnit
  let := hP.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot P) := .of_finite F _
  let : Fintype (MaximalSpectrum (AdjoinRoot P)) := Fintype.ofFinite _
  let length (q : MaximalSpectrum (AdjoinRoot P)) : ℕ :=
    (Module.length (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal)).toNat
  let N (q : MaximalSpectrum (AdjoinRoot P)) : Fˣ :=
    Units.map (Algebra.norm F) (residueComplementUnit P h1 q)
  have hroot : (AdjoinRoot.root P) ^ p = AdjoinRoot.of P (a : F) := by
    have hr := AdjoinRoot.eval₂_root P
    simpa only [P, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] using hr
  have hbranch : ∀ q : MaximalSpectrum (AdjoinRoot P),
      m • graphSymbol F a (N q) = 0 := by
    intro q
    let E := AdjoinRoot P ⧸ q.asIdeal
    let : CharZero E := Algebra.charZero_of_charZero F E
    have hpow : (residueRootUnit P h0 q) ^ p =
        Units.map (algebraMap F E).toMonoidHom a := by
      apply Units.ext
      change (Ideal.Quotient.mk q.asIdeal (rootUnit P h0)) ^ p =
        algebraMap F E (a : F)
      rw [rootUnit_val, ← map_pow, hroot]
      rfl
    have hE : m • graphSymbol E (Units.map (algebraMap F E).toMonoidHom a)
        (residueComplementUnit P h1 q) = 0 := by
      rw [← hpow, graphSymbol_pow_left, ← mul_smul]
      exact h E (residueRootUnit P h0 q) (residueComplementUnit P h1 q)
        (residueComplementUnit_val P h0 h1 q)
    have ht := congrArg (corestriction (k := F)) hE
    simpa only [map_nsmul, corestriction_graphSymbol_prepend, map_zero] using ht
  have hnorm : (∏ q : MaximalSpectrum (AdjoinRoot P), N q ^ length q) = b := by
    apply Units.ext
    simp only [Units.coe_prod, Units.val_pow_eq_pow_val, Units.coe_map, N]
    change (∏ q : MaximalSpectrum (AdjoinRoot P),
      Algebra.norm F (residueComplementUnit P h1 q : AdjoinRoot P ⧸ q.asIdeal) ^
        length q) = (b : F)
    rw [prod_residueComplement_norm_eq_eval_one P hP h1]
    simpa only [P, eval_sub, eval_pow, eval_X, eval_C, one_pow] using hab.symm
  rw [← hnorm, graphSymbol_prod_right, Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro q _
  rw [graphSymbol_pow_right, smul_comm m, hbranch q, smul_zero]

/-- A positive universal annihilator forces the actual complementary-unit
graph symbols to vanish, by applying the whole root polynomial once. -/
theorem graphSymbol_eq_zero_of_universal_annihilator (n : ℕ) (hn : 0 < n)
    (h : UniversalSteinbergAnnihilator.{u} n)
    (F : Type u) [Field F] [CharZero F] (a b : Fˣ)
    (hab : (b : F) = 1 - (a : F)) : graphSymbol F a b = 0 := by
  have h1 : UniversalSteinbergAnnihilator.{u} 1 :=
    remove_positive_factor 1 n hn (by simpa only [one_mul] using h)
  simpa only [one_smul] using h1 F a b hab

end Motivic.WeightTwoSteinbergTorsion
