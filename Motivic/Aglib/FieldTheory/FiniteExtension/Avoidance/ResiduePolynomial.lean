/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.WholeFiber
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Full-fiber avoidance for finite residue-field polynomials

A residue-field polynomial is placed in the finite free coefficient extension
of the original parameter algebra. Its norm is nonzero because this coefficient
extension is the polynomial ring over the residue field, hence a domain.
After specializing over a sufficiently large finite extension, the polynomial
is a unit on the entire tensor fiber, not just nonzero on one chosen component.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace MvPolynomial

universe u v w

/-- The coefficient extension in the order used for its finite free
module structure over the original parameter ring. -/
def residueCoefficientEquiv
    (k : Type u) [Field k] (K : Type v) [Field K] [Algebra k K]
    (σ : Type w) :
    (MvPolynomial σ k ⊗[k] K) ≃+* MvPolynomial σ K :=
  (Algebra.TensorProduct.comm k (MvPolynomial σ k) K).toRingEquiv.trans
    (algebraTensorAlgEquiv k K).toRingEquiv

/-- For an actual nonzero polynomial over a finite residue extension, every
sufficiently large extension of the ground field admits a parameter avoiding
all branches of the closed fiber. No infinite-field instance is introduced. -/
theorem exists_isUnit_residuePolynomial_finiteExtension
    (k : Type u) [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (K : Type v) [Field K] [Algebra k K] [Module.Finite k K]
    {σ : Type w} [Finite σ] (q : MvPolynomial σ K) (hq : q ≠ 0) :
    ∃ N : ℕ, ∀ (n : ℕ) [NeZero n], N < n →
      ∃ c : σ → FiniteField.Extension k p n,
        let : Algebra (MvPolynomial σ k) (FiniteField.Extension k p n) :=
          (eval₂Hom (algebraMap k (FiniteField.Extension k p n)) c).toAlgebra
        IsUnit (1 ⊗ₜ[MvPolynomial σ k] (residueCoefficientEquiv k K σ).symm q :
          FiniteField.Extension k p n ⊗[MvPolynomial σ k]
            (MvPolynomial σ k ⊗[k] K)) := by
  let e := residueCoefficientEquiv k K σ
  let : IsDomain (MvPolynomial σ k ⊗[k] K) :=
    e.toMulEquiv.isDomain (MvPolynomial σ K)
  let b := e.symm q
  have hb : b ≠ 0 := fun h => hq (by simpa [b] using congrArg e h)
  refine ⟨(Algebra.norm (MvPolynomial σ k) b).totalDegree, ?_⟩
  intro n _ hn
  exact Algebra.exists_isUnit_wholeFiber_finiteExtension k p
    (MvPolynomial σ k ⊗[k] K) b hb n hn

/-- A single parameter avoids every branch of every member of a finite family
of residue-polynomial conditions. The bound uses the product of their actual
norm polynomials, rather than coefficientwise linear-functional witnesses. -/
theorem exists_isUnit_simultaneous_residuePolynomials_finiteExtension
    (k : Type u) [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {ι : Type v} [Finite ι] (K : ι → Type v)
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module.Finite k (K i)]
    {σ : Type w} [Finite σ]
    (q : (i : ι) → MvPolynomial σ (K i)) (hq : ∀ i, q i ≠ 0) :
    ∃ N : ℕ, ∀ (n : ℕ) [NeZero n], N < n →
      ∃ c : σ → FiniteField.Extension k p n,
        let : Algebra (MvPolynomial σ k) (FiniteField.Extension k p n) :=
          (eval₂Hom (algebraMap k (FiniteField.Extension k p n)) c).toAlgebra
        ∀ i, IsUnit
          (1 ⊗ₜ[MvPolynomial σ k] (residueCoefficientEquiv k (K i) σ).symm (q i) :
            FiniteField.Extension k p n ⊗[MvPolynomial σ k]
              (MvPolynomial σ k ⊗[k] K i)) := by
  classical
  let := Fintype.ofFinite ι
  let e := fun i => residueCoefficientEquiv k (K i) σ
  let : ∀ i, IsDomain (MvPolynomial σ k ⊗[k] K i) :=
    fun i => (e i).toMulEquiv.isDomain (MvPolynomial σ (K i))
  let b := fun i => (e i).symm (q i)
  have hb : ∀ i, b i ≠ 0 := by
    intro i h
    exact hq i (by simpa [b] using congrArg (e i) h)
  let Q : ι → MvPolynomial σ k := fun i => Algebra.norm (MvPolynomial σ k) (b i)
  have hQ : ∀ i, Q i ≠ 0 := fun i => Algebra.norm_ne_zero_iff.mpr (hb i)
  have hprod : (∏ i, Q i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hQ i
  refine ⟨(∏ i, Q i).totalDegree, ?_⟩
  intro n _ hn
  obtain ⟨c, hc⟩ := exists_eval₂_ne_zero_finiteExtension k p (∏ i, Q i) hprod n hn
  refine ⟨c, ?_⟩
  let : Algebra (MvPolynomial σ k) (FiniteField.Extension k p n) :=
    (eval₂Hom (algebraMap k (FiniteField.Extension k p n)) c).toAlgebra
  dsimp only
  intro i
  apply Algebra.isUnit_of_norm_ne_zero (L := FiniteField.Extension k p n)
    (B := FiniteField.Extension k p n ⊗[MvPolynomial σ k]
      (MvPolynomial σ k ⊗[k] K i))
  rw [Algebra.norm_one_tmul]
  change (eval₂Hom (algebraMap k (FiniteField.Extension k p n)) c) (Q i) ≠ 0
  change (eval₂Hom (algebraMap k (FiniteField.Extension k p n)) c) (∏ j, Q j) ≠ 0 at hc
  rw [map_prod] at hc
  exact Finset.prod_ne_zero_iff.mp hc i (Finset.mem_univ i)

end MvPolynomial
