/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.AlgebraicIndependent.PolynomialQuotientFractionTrdeg
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.TensorProduct.Finite
public import Lean.Util.CollectAxioms

/-! # Polynomial coefficient-chart fraction-field regression tests -/

@[expose] public noncomputable section

universe u

namespace Motivic.MotivicTest.PolynomialQuotientFractionTrdeg

/-- Direct use for the normalized weight index, without renaming variables. -/
theorem normalized_weight_bound
    {k R : Type u} [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    {d : ℕ} (i₀ : Fin d)
    (P : Ideal (MvPolynomial {i : Fin d // i ≠ i₀} R)) [P.IsPrime] :
    Algebra.trdeg k (FractionRing (MvPolynomial {i : Fin d // i ≠ i₀} R ⧸ P)) ≤
      Algebra.trdeg k R + Fintype.card {i : Fin d // i ≠ i₀} :=
  P.trdeg_fractionRing_mvPolynomial_quotient_le

/-- The actual denominator can be a coefficient, with no nonvanishing input. -/
theorem normalized_coefficient_localization_bound
    {k R : Type u} [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    {d : ℕ} (i₀ : Fin d) (t : R)
    (P : Ideal (Localization.Away (MvPolynomial.C t : MvPolynomial
      {i : Fin d // i ≠ i₀} R))) [P.IsPrime] :
    Algebra.trdeg k (FractionRing (Localization.Away (MvPolynomial.C t : MvPolynomial
      {i : Fin d // i ≠ i₀} R) ⧸ P)) ≤
      Algebra.trdeg k R + Fintype.card {i : Fin d // i ≠ i₀} :=
  P.trdeg_fractionRing_localized_mvPolynomial_quotient_le (MvPolynomial.C t)

/-- A concrete coefficient specialization that kills a nonzero coefficient. -/
def specializeCoefficient (k : Type u) [Field k] (n : ℕ) :
    MvPolynomial (Fin n) (Polynomial k) →ₐ[k] k :=
  MvPolynomial.aevalTower (Polynomial.aeval (0 : k)) fun _ => 0

/-- This test exercises a genuinely noninjective coefficient map. -/
theorem coefficient_specialization_kills_nonzero
    (k : Type u) [Field k] (n : ℕ) :
    (MvPolynomial.C (Polynomial.X : Polynomial k) : MvPolynomial (Fin n) (Polynomial k)) ≠ 0 ∧
      specializeCoefficient k n (MvPolynomial.C Polynomial.X) = 0 := by
  constructor
  · simpa only [ne_eq, MvPolynomial.C_eq_zero] using
      (Polynomial.X_ne_zero : (Polynomial.X : Polynomial k) ≠ 0)
  · simp [specializeCoefficient]

/-- The fraction-field estimate accepts that specialization directly. -/
theorem coefficient_specialization_bound
    (k : Type u) [Field k] (n : ℕ) :
    Algebra.trdeg k k ≤ Algebra.trdeg k (Polynomial k) + n := by
  have hs : Function.Surjective (specializeCoefficient k n) := by
    intro a
    exact ⟨algebraMap k _ a, (specializeCoefficient k n).commutes a⟩
  simpa using (specializeCoefficient k n).trdeg_fractionRing_le_of_mvPolynomial_surjective
    (K := k) hs

/-- Direct normalized-chart use with arbitrary finite coefficient algebra. -/
theorem finite_normalized_coefficient_bound
    {k R B : Type u} [Field k] [CommRing R] [IsDomain R] [CommRing B]
    [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B] [Module.Finite R B]
    {d : ℕ} (i₀ : Fin d) (t : B)
    (P : Ideal (Localization.Away (MvPolynomial.C t : MvPolynomial
      {i : Fin d // i ≠ i₀} B))) [P.IsPrime] :
    Algebra.trdeg k (FractionRing (Localization.Away (MvPolynomial.C t : MvPolynomial
      {i : Fin d // i ≠ i₀} B) ⧸ P)) ≤
      Algebra.trdeg k R + Fintype.card {i : Fin d // i ≠ i₀} :=
  P.trdeg_fractionRing_finite_localized_mvPolynomial_quotient_le (R := R) (MvPolynomial.C t)

/-- A localized polynomial chart with a disconnected finite coefficient algebra. -/
def productCoefficientMap (k : Type u) [Field k] :
    Localization.Away (1 : MvPolynomial Unit (k × k)) →ₐ[k] k :=
  IsLocalization.Away.liftAlgHom
    (f := MvPolynomial.aevalTower (AlgHom.fst k k k) fun _ : Unit => 0) 1
    (by simpa only [map_one] using (isUnit_one : IsUnit (1 : k)))

/-- The actual finite-coefficient producer applies to that disconnected chart. -/
theorem product_coefficient_bound (k : Type u) [Field k] :
    Algebra.trdeg k k ≤ Algebra.trdeg k k + 1 := by
  have hs : Function.Surjective (productCoefficientMap k) := by
    intro a
    exact ⟨algebraMap k _ a, (productCoefficientMap k).commutes a⟩
  exact (productCoefficientMap k).trdeg_fractionRing_le_of_finite_localized_mvPolynomial_surjective
    (R := k) (K := k) 1 hs

/-- The coefficient algebra in the preceding application is genuinely not a domain. -/
theorem product_coefficients_not_domain (k : Type u) [Field k] : ¬ IsDomain (k × k) := by
  intro h
  have := h
  have h₁ : (1, 0) ≠ (0 : k × k) := by simp
  have h₂ : (0, 1) ≠ (0 : k × k) := by simp
  have hm := mul_ne_zero h₁ h₂
  simp at hm

open scoped TensorProduct in
/-- Closed-point residue-field base change is finite, not necessarily a domain;
the actual localized prime quotient nevertheless has the required bound. -/
theorem finite_residue_tensor_coefficient_bound
    {k R L : Type u} [Field k] [CommRing R] [IsDomain R] [Field L]
    [Algebra k R] [Algebra k L] [Module.Finite k L]
    {d : ℕ} (i₀ : Fin d) (t : R ⊗[k] L)
    (P : Ideal (Localization.Away (MvPolynomial.C t : MvPolynomial
      {i : Fin d // i ≠ i₀} (R ⊗[k] L)))) [P.IsPrime] :
    Algebra.trdeg k (FractionRing (Localization.Away (MvPolynomial.C t : MvPolynomial
      {i : Fin d // i ≠ i₀} (R ⊗[k] L)) ⧸ P)) ≤
      Algebra.trdeg k R + Fintype.card {i : Fin d // i ≠ i₀} :=
  P.trdeg_fractionRing_finite_localized_mvPolynomial_quotient_le (R := R) (MvPolynomial.C t)

open Lean in
run_cmd do
  for name in #[``Algebra.trdeg_mvPolynomial_fintype_eq_add,
      ``AlgHom.trdeg_fractionRing_le_of_surjective,
      ``AlgHom.trdeg_fractionRing_le_of_mvPolynomial_surjective,
      ``AlgHom.trdeg_fractionRing_le_of_localized_mvPolynomial_surjective,
      ``Ideal.trdeg_fractionRing_mvPolynomial_quotient_le,
      ``Ideal.trdeg_fractionRing_localized_mvPolynomial_quotient_le,
      ``normalized_weight_bound, ``normalized_coefficient_localization_bound,
      ``specializeCoefficient, ``coefficient_specialization_kills_nonzero,
      ``coefficient_specialization_bound,
      ``AlgHom.trdeg_fractionRing_le_of_integral_localization_surjective,
      ``AlgHom.trdeg_fractionRing_le_of_finite_localized_mvPolynomial_surjective,
      ``Ideal.trdeg_fractionRing_finite_localized_mvPolynomial_quotient_le,
      ``finite_normalized_coefficient_bound, ``productCoefficientMap,
      ``product_coefficient_bound, ``product_coefficients_not_domain,
      ``finite_residue_tensor_coefficient_bound] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Polynomial quotient fraction-field audit passed: standard foundations only."

end Motivic.MotivicTest.PolynomialQuotientFractionTrdeg
