/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.FiniteExtensionPolynomialAvoidance
public import Motivic.Aglib.RingTheory.PolynomialFiberNorm
public import Mathlib.RingTheory.Norm.Basic

/-!
# Finite-extension avoidance on the entire finite fiber

For a finite free domain over the original parameter polynomial ring, the
actual determinant norm of a nonzero function cuts out a nonempty principal
open. Every sufficiently large finite extension has a parameter in this open.
The function then becomes a unit in the whole evaluation fiber, including
all branches and nilpotent structure. Mere nonvanishing in a tensor product
would not imply this conclusion.

This is a parameter-algebra leaf. It does not construct the finite free
parameter algebra required by a particular geometric presentation.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra

universe u v w

/-- A nonzero determinant norm makes multiplication surjective, hence the
original element a unit. The finite algebra need not be reduced or a domain. -/
theorem isUnit_of_norm_ne_zero
    {L : Type u} [Field L] {B : Type v} [CommRing B] [Algebra L B]
    [Module.Finite L B] (b : B) (hb : norm L b ≠ 0) : IsUnit b := by
  have hd : IsUnit (Algebra.lmul L B b).det := isUnit_iff_ne_zero.mpr hb
  obtain ⟨c, hc⟩ := (LinearMap.equivOfIsUnitDet hd).surjective 1
  have hbc : b * c = 1 := by
    simpa only [LinearMap.equivOfIsUnitDet_apply, Algebra.coe_lmul_eq_mul,
      LinearMap.mul_apply'] using hc
  exact isUnit_iff_exists_inv.mpr ⟨c, hbc⟩

/-- Nonzero norm means nonvanishing at every field-valued branch, not merely
at one branch. This includes all prime residue maps of the finite fiber. -/
theorem map_ne_zero_of_norm_ne_zero
    {L : Type u} [Field L] {B : Type v} [CommRing B] [Algebra L B]
    [Module.Finite L B] (b : B) (hb : norm L b ≠ 0)
    {E : Type w} [Field E] (φ : B →+* E) : φ b ≠ 0 :=
  ((isUnit_of_norm_ne_zero b hb).map φ).ne_zero

/-- All closed-fiber branches are avoided simultaneously over every sufficiently
large extension. The threshold is the degree of the actual determinant norm.
No separability or reducedness of the evaluation fibers is assumed. -/
theorem exists_isUnit_wholeFiber_finiteExtension
    (k : Type u) [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {σ : Type w} [Finite σ]
    (B : Type v) [CommRing B] [IsDomain B]
    [Algebra (MvPolynomial σ k) B]
    [Module.Free (MvPolynomial σ k) B] [Module.Finite (MvPolynomial σ k) B]
    (b : B) (hb : b ≠ 0) (n : ℕ) [NeZero n]
    (hn : (norm (MvPolynomial σ k) b).totalDegree < n) :
    ∃ c : σ → FiniteField.Extension k p n,
      let : Algebra (MvPolynomial σ k) (FiniteField.Extension k p n) :=
        (MvPolynomial.eval₂Hom (algebraMap k (FiniteField.Extension k p n)) c).toAlgebra
      IsUnit (1 ⊗ₜ[MvPolynomial σ k] b :
        FiniteField.Extension k p n ⊗[MvPolynomial σ k] B) := by
  obtain ⟨c, hc⟩ := MvPolynomial.exists_eval₂_ne_zero_finiteExtension k p
    (norm (MvPolynomial σ k) b) (norm_ne_zero_iff.mpr hb) n hn
  refine ⟨c, ?_⟩
  let : Algebra (MvPolynomial σ k) (FiniteField.Extension k p n) :=
    (MvPolynomial.eval₂Hom (algebraMap k (FiniteField.Extension k p n)) c).toAlgebra
  apply isUnit_of_norm_ne_zero (L := FiniteField.Extension k p n)
  rw [norm_one_tmul]
  exact hc

end Algebra
