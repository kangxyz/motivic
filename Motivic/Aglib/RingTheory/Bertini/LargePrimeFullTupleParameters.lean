/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.SimultaneousFullTuplePolynomial
public import Motivic.Aglib.RingTheory.TensorProduct.ScalarExtension.LargePrime

/-! # Two unchanged prime extensions satisfy the full original parameter condition

The output retains every branch of both determinant fibers. The differential
and projective geometric base-change identifications remain separate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Module _root_.MvPolynomial AlgebraicGeometry
open scoped TensorProduct

namespace QuadraticIncidence

universe u

/-- A norm condition gives a unit on the entire actual specialized coefficient fiber. -/
theorem isUnit_residueParameter_of_eval₂_norm_ne_zero
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Module.Finite k K] [Algebra k L]
    {τ : Type u} (T : MvPolynomial τ K) (c : τ → L)
    (h : eval₂ (algebraMap k L) c (residueParameterNorm k K T) ≠ 0) :
    let : Algebra (MvPolynomial τ k) L := (eval₂Hom (algebraMap k L) c).toAlgebra
    IsUnit (1 ⊗ₜ[MvPolynomial τ k] (residueCoefficientEquiv k K τ).symm T :
      L ⊗[MvPolynomial τ k] (MvPolynomial τ k ⊗[k] K)) := by
  let : Algebra (MvPolynomial τ k) L := (eval₂Hom (algebraMap k L) c).toAlgebra
  apply Algebra.isUnit_of_norm_ne_zero (L := L)
    (B := L ⊗[MvPolynomial τ k] (MvPolynomial τ k ⊗[k] K))
  rw [Algebra.norm_one_tmul]
  exact h

/-- Both actual determinant norms and all four relation/open factors hold on
one full tuple over each of the same two large prime extensions. -/
theorem exists_two_prime_fullTuple_parameters
    (k R : Type u) [Field k] [Finite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (x : PrimeSpectrum R) [x.asIdeal.IsMaximal]
    {σ : Type u} [Fintype σ] (d : ℕ)
    (B : Basis (Fin (d + 1)) x.asIdeal.ResidueField
      (x.asIdeal.ResidueField ⊗[R] KaehlerDifferential k R))
    (J : restrictTotalDegree σ x.asIdeal.ResidueField 2 →ₗ[x.asIdeal.ResidueField]
      (x.asIdeal.ResidueField ⊗[R] KaehlerDifferential k R))
    (hJ : Function.Surjective J)
    (F : MvPolynomial (Fin (d + 1) × Exponent σ) k)
    (f Q q : MvPolynomial (Fin d × Exponent σ) k)
    (hF : F ≠ 0) (hf : f ≠ 0) (hQ : Q ≠ 0) (hq : q ≠ 0) (N : ℕ) :
    ∃ n m : ℕ, N < n ∧ N < m ∧ n.Coprime m ∧
      ∀ (r : ℕ) [NeZero r], r = n ∨ r = m →
        let L := ULift.{u} (FiniteField.Extension k p r)
        Module.finrank k L = r ∧ IsDomain (R ⊗[k] L) ∧
          (∃! y : PrimeSpectrum (R ⊗[k] L),
            PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x) ∧
          ∃ (a : Exponent σ → L) (c : Fin d × Exponent σ → L),
            eval₂ (algebraMap k L) (prependParameters L d a c) F ≠ 0 ∧
            eval₂ (algebraMap k L) c f ≠ 0 ∧
            eval₂ (algebraMap k L) c Q ≠ 0 ∧
            eval₂ (algebraMap k L) c q ≠ 0 ∧
            (let : Algebra (MvPolynomial (Fin (d + 1) × Exponent σ) k) L :=
              (eval₂Hom (algebraMap k L) (prependParameters L d a c)).toAlgebra
             IsUnit (1 ⊗ₜ[MvPolynomial (Fin (d + 1) × Exponent σ) k]
               (residueCoefficientEquiv k x.asIdeal.ResidueField _).symm
                 (fullSelectedDeterminant (d + 1) B J) :
               L ⊗[MvPolynomial (Fin (d + 1) × Exponent σ) k]
                 (MvPolynomial (Fin (d + 1) × Exponent σ) k ⊗[k] x.asIdeal.ResidueField))) ∧
            (let : Algebra (MvPolynomial (Fin d × Exponent σ) k) L :=
              (eval₂Hom (algebraMap k L) c).toAlgebra
             IsUnit (1 ⊗ₜ[MvPolynomial (Fin d × Exponent σ) k]
               (residueCoefficientEquiv k x.asIdeal.ResidueField _).symm
                 (selectedDeterminant d B J) :
               L ⊗[MvPolynomial (Fin d × Exponent σ) k]
                 (MvPolynomial (Fin d × Exponent σ) k ⊗[k] x.asIdeal.ResidueField))) := by
  let κ := x.asIdeal.ResidueField
  let : Module.Finite k κ := ClosedPoint.residueField_finite k R x
  let E := residueParameterNorm k κ (fullSelectedDeterminant (d + 1) B J)
  let D := residueParameterNorm k κ (selectedDeterminant d B J)
  let H := simultaneousFullTuplePolynomial d F E f D Q q
  have hH : H ≠ 0 := simultaneousFullTuplePolynomial_selectedDeterminants_ne_zero
    k κ d B J hJ F f Q q hF hf hQ hq
  obtain ⟨n, m, _, _, hn, hm, _, hnm, h⟩ :=
    Algebra.TensorProduct.exists_two_large_prime_scalar_extensions k R p x H hH N
  refine ⟨n, m, hn, hm, hnm, ?_⟩
  intro r _ hr
  obtain ⟨hdegree, hdomain, hunique, z, hz⟩ := h r hr
  let L := ULift.{u} (FiniteField.Extension k p r)
  let a : Exponent σ → L := fun e => z (0, e)
  let c : Fin d × Exponent σ → L := fun q => z (q.1.succ, q.2)
  have hsplit : prependParameters L d a c = z := by
    funext q
    rcases q with ⟨i, e⟩
    exact Fin.cases rfl (fun _ => rfl) i
  have hprod : eval₂ (algebraMap k L) z F * eval₂ (algebraMap k L) z E *
      (eval₂ (algebraMap k L) c f * eval₂ (algebraMap k L) c D *
        eval₂ (algebraMap k L) c Q * eval₂ (algebraMap k L) c q) ≠ 0 := by
    simpa [H, simultaneousFullTuplePolynomial, eval₂_rename, originalRowIndex,
      Function.comp_def, c] using hz
  have hFE := (mul_ne_zero_iff.mp hprod).1
  have htail := (mul_ne_zero_iff.mp hprod).2
  have hfDQ := (mul_ne_zero_iff.mp htail).1
  have hfD := (mul_ne_zero_iff.mp hfDQ).1
  refine ⟨hdegree, hdomain, hunique, a, c, ?_, (mul_ne_zero_iff.mp hfD).1,
    (mul_ne_zero_iff.mp hfDQ).2, (mul_ne_zero_iff.mp htail).2, ?_, ?_⟩
  · change eval₂ (algebraMap k L) (prependParameters L d a c) F ≠ 0
    rw [hsplit]
    exact (mul_ne_zero_iff.mp hFE).1
  · apply isUnit_residueParameter_of_eval₂_norm_ne_zero
    change eval₂ (algebraMap k L) (prependParameters L d a c) E ≠ 0
    rw [hsplit]
    exact (mul_ne_zero_iff.mp hFE).2
  · exact isUnit_residueParameter_of_eval₂_norm_ne_zero k κ L _ c
      (mul_ne_zero_iff.mp hfD).2

end QuadraticIncidence
