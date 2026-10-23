/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-! # Actual polynomial interpolation for zero-section neighborhoods

The coefficient ring is arbitrary, including nilpotents and disconnected
spectra. The two prescribed residues are at the whole polynomial boundary
and at zero. No polynomial section or interpolation is assumed to exist.
-/

@[expose] public noncomputable section

open Polynomial

universe u
namespace Polynomial.ZeroNeighborhoodInterpolation
variable {R : Type u} [CommRing R]

/-- A global numerator residue; only the boundary value at zero is inverted. -/
def numeratorResidue (f : R[X]) (a : R) (u : Rˣ) : R[X] :=
  1 + f * C ((↑(u⁻¹) : R) * (-a - 1))

/-- The genuine polynomial divided difference, defined over the original ring. -/
def dividedDifference (f : R[X]) (a : R) : R[X] := f /ₘ (X - C a)

lemma dividedDifference_mul (f : R[X]) (a : R) :
    (X - C a) * dividedDifference f a = f - C (f.eval a) := by
  have h := modByMonic_add_div f (X - C a)
  rw [modByMonic_X_sub_C_eq_C_eval] at h
  exact eq_sub_of_add_eq' h

/-- The denominator residue uses the actual unit `f(a)` and corrects its value at zero. -/
def denominatorResidue (f : R[X]) (a : R) (u v : Rˣ) : R[X] :=
  -C (↑(v⁻¹) : R) * dividedDifference f a +
    f * C ((↑(u⁻¹) : R) * (1 + (↑(v⁻¹) : R) * (dividedDifference f a).eval 0))

lemma numeratorResidue_eval_zero (f : R[X]) (a : R) (u : Rˣ)
    (h0 : f.eval 0 = ↑u) : (numeratorResidue f a u).eval 0 = -a := by
  simp only [numeratorResidue, eval_add, eval_one, eval_mul, eval_C, h0]
  rw [← mul_assoc]
  simp

lemma numeratorResidue_boundary (f : R[X]) (a : R) (u : Rˣ) :
    f ∣ numeratorResidue f a u - 1 := by
  exact ⟨C ((↑(u⁻¹) : R) * (-a - 1)), by simp [numeratorResidue]⟩

lemma denominatorResidue_eval_zero (f : R[X]) (a : R) (u v : Rˣ)
    (h0 : f.eval 0 = ↑u) : (denominatorResidue f a u v).eval 0 = 1 := by
  simp only [denominatorResidue, eval_add, eval_mul, eval_neg, eval_C, h0]
  rw [← mul_assoc (↑u : R)]
  simp

lemma denominatorResidue_boundary (f : R[X]) (a : R) (u v : Rˣ)
    (ha : f.eval a = ↑v) : f ∣ (X - C a) * denominatorResidue f a u v - 1 := by
  refine ⟨-C (↑(v⁻¹) : R) + (X - C a) *
    C ((↑(u⁻¹) : R) * (1 + (↑(v⁻¹) : R) * (dividedDifference f a).eval 0)), ?_⟩
  have hdiv := dividedDifference_mul f a
  have hu : C (↑(v⁻¹) : R) * C (f.eval a) = (1 : R[X]) := by
    rw [ha, ← C_mul]
    simp
  dsimp only [denominatorResidue]
  linear_combination -C (↑(v⁻¹) : R) * hdiv + hu

/-- Raise the leading degree without changing either prescribed boundary residue. -/
def monicLift (f r : R[X]) (N : ℕ) : R[X] := r + X * f * X ^ N

lemma monicLift_eval_zero (f r : R[X]) (N : ℕ) :
    (monicLift f r N).eval 0 = r.eval 0 := by simp [monicLift]

lemma monicLift_boundary (f r : R[X]) (N : ℕ) : f ∣ monicLift f r N - r := by
  refine ⟨X * X ^ N, ?_⟩
  dsimp only [monicLift]
  ring

lemma monicLift_monic_natDegree [Nontrivial R] (f r : R[X]) (hf : f.Monic)
    (N : ℕ) (hr : r.natDegree ≤ N) :
    (monicLift f r N).Monic ∧ (monicLift f r N).natDegree = f.natDegree + N + 1 := by
  have hm : (X * f * X ^ N).Monic := (monic_X.mul hf).mul (monic_X.pow N)
  have hd : (X * f * X ^ N).natDegree = f.natDegree + N + 1 := by
    rw [Monic.natDegree_mul (monic_X.mul hf) (monic_X.pow N),
      Monic.natDegree_mul monic_X hf, natDegree_X, natDegree_X_pow]
    omega
  have hr' : r.natDegree < (X * f * X ^ N).natDegree := by rw [hd]; omega
  exact ⟨hm.add_of_right (degree_lt_degree hr'),
    (natDegree_add_eq_right_of_natDegree_lt hr').trans hd⟩

/-- Actual two-boundary interpolation, with matching degrees for the diagonal pencil. -/
theorem exists_monic_pair [Nontrivial R] (f : R[X]) (hf : f.Monic) (a : R)
    (h0 : IsUnit (f.eval 0)) (ha : IsUnit (f.eval a)) :
    ∃ d g : R[X], d.Monic ∧ g.Monic ∧ g.natDegree = d.natDegree + 1 ∧
      d.eval 0 = 1 ∧ g.eval 0 = -a ∧
      f ∣ (X - C a) * d - 1 ∧ f ∣ g - 1 := by
  obtain ⟨u, hu⟩ := h0
  obtain ⟨v, hv⟩ := ha
  let d0 := denominatorResidue f a u v
  let g0 := numeratorResidue f a u
  let N := max d0.natDegree g0.natDegree
  let d := monicLift f d0 N
  let g := monicLift f g0 (N + 1)
  have hd := monicLift_monic_natDegree f d0 hf N (Nat.le_max_left _ _)
  have hg := monicLift_monic_natDegree f g0 hf (N + 1)
    ((Nat.le_max_right _ _).trans (Nat.le_succ N))
  refine ⟨d, g, hd.1, hg.1, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [d, g]
    rw [hd.2, hg.2]
    omega
  · exact (monicLift_eval_zero f d0 N).trans
      (denominatorResidue_eval_zero f a u v hu.symm)
  · exact (monicLift_eval_zero f g0 (N + 1)).trans
      (numeratorResidue_eval_zero f a u hu.symm)
  · have h1 := dvd_mul_of_dvd_right (monicLift_boundary f d0 N) (X - C a)
    have h2 := denominatorResidue_boundary f a u v hv.symm
    convert dvd_add h1 h2 using 1
    dsimp only [d, d0]
    ring
  · have h1 := monicLift_boundary f g0 (N + 1)
    have h2 := numeratorResidue_boundary f a u
    convert dvd_add h1 h2 using 1
    dsimp only [g, g0]
    ring

end Polynomial.ZeroNeighborhoodInterpolation
