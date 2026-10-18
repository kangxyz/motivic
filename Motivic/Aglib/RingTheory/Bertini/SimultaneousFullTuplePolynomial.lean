/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.AuxiliaryQuadraticParameter
public import Motivic.Aglib.RingTheory.Bertini.QuadraticFullSelectedPointOpen
public import Motivic.Aglib.RingTheory.FiniteExtensionResiduePolynomialAvoidance

/-! # One polynomial controls the auxiliary row and all original rows

The determinant norms are formed over the original ground parameter algebra,
before choosing a finite extension. No cotangent base-change identification is
asserted here.
-/

@[expose] public noncomputable section

open Module MvPolynomial
open scoped TensorProduct

namespace QuadraticIncidence

universe u

/-- Include the original rows without changing any of their monomial indices. -/
def originalRowIndex {N : Type u} (d : ℕ) : Fin d × N → Fin (d + 1) × N :=
  fun q => (q.1.succ, q.2)

theorem originalRowIndex_injective {N : Type u} (d : ℕ) :
    Function.Injective (originalRowIndex (N := N) d) := by
  rintro ⟨i, e⟩ ⟨j, f⟩ h
  have hi : i = j := Fin.succ_injective d (congrArg Prod.fst h)
  have he : e = f := congrArg Prod.snd h
  exact Prod.ext hi he

/-- The full tuple retains ambient infinity and the full determinant, while its
original rows retain off-diagonal, diagonal, closed infinity and requested opens. -/
def simultaneousFullTuplePolynomial
    {k N : Type u} [CommRing k] (d : ℕ)
    (F E : MvPolynomial (Fin (d + 1) × N) k)
    (f D Q q : MvPolynomial (Fin d × N) k) :
    MvPolynomial (Fin (d + 1) × N) k :=
  F * E * rename (originalRowIndex d) (f * D * Q * q)

theorem simultaneousFullTuplePolynomial_ne_zero
    {k N : Type u} [CommRing k] [IsDomain k] (d : ℕ)
    (F E : MvPolynomial (Fin (d + 1) × N) k)
    (f D Q q : MvPolynomial (Fin d × N) k)
    (hF : F ≠ 0) (hE : E ≠ 0) (hf : f ≠ 0) (hD : D ≠ 0)
    (hQ : Q ≠ 0) (hq : q ≠ 0) :
    simultaneousFullTuplePolynomial d F E f D Q q ≠ 0 := by
  apply mul_ne_zero (mul_ne_zero hF hE)
  intro h
  apply mul_ne_zero (mul_ne_zero (mul_ne_zero hf hD) hQ) hq
  exact (rename_injective _ (originalRowIndex_injective d)) (by simpa using h)

/-- Evaluation uses the literal original rows, also for scalar-valued parameters. -/
theorem eval₂_rename_originalRows
    {k L N : Type u} [CommRing k] [CommRing L] (φ : k →+* L) (d : ℕ)
    (a : N → L) (c : Fin d × N → L) (q : MvPolynomial (Fin d × N) k) :
    eval₂ φ (prependParameters L d a c) (rename (originalRowIndex d) q) =
      eval₂ φ c q := by
  rw [eval₂_rename]
  rfl

/-- The norm of the actual residue polynomial, in the original parameter algebra. -/
def residueParameterNorm
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {τ : Type u} (T : MvPolynomial τ K) : MvPolynomial τ k :=
  Algebra.norm (MvPolynomial τ k) ((residueCoefficientEquiv k K τ).symm T)

theorem residueParameterNorm_ne_zero
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    {τ : Type u} (T : MvPolynomial τ K) (hT : T ≠ 0) :
    residueParameterNorm k K T ≠ 0 := by
  let e := residueCoefficientEquiv k K τ
  let : IsDomain (MvPolynomial τ k ⊗[k] K) := e.toMulEquiv.isDomain _
  apply Algebra.norm_ne_zero_iff.mpr
  intro h
  exact hT (by simpa [e] using congrArg e h)

/-- Both actual selected-derivative determinants enter the same nonzero ground
polynomial before extension; all geometric relation factors are retained. -/
theorem simultaneousFullTuplePolynomial_selectedDeterminants_ne_zero
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    {σ V : Type u} [Fintype σ] [AddCommGroup V] [Module K V]
    (d : ℕ) (B : Basis (Fin (d + 1)) K V)
    (J : restrictTotalDegree σ K 2 →ₗ[K] V) (hJ : Function.Surjective J)
    (F : MvPolynomial (Fin (d + 1) × Exponent σ) k)
    (f Q q : MvPolynomial (Fin d × Exponent σ) k)
    (hF : F ≠ 0) (hf : f ≠ 0) (hQ : Q ≠ 0) (hq : q ≠ 0) :
    simultaneousFullTuplePolynomial d F
      (residueParameterNorm k K (fullSelectedDeterminant (d + 1) B J)) f
      (residueParameterNorm k K (selectedDeterminant d B J)) Q q ≠ 0 := by
  exact simultaneousFullTuplePolynomial_ne_zero d _ _ _ _ _ _ hF
    (residueParameterNorm_ne_zero k K _ (fullSelectedDeterminant_ne_zero _ B J hJ)) hf
    (residueParameterNorm_ne_zero k K _ (selectedDeterminant_ne_zero d B J hJ)) hQ hq

end QuadraticIncidence
