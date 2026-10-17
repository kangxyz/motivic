/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.ProjectiveEvaluationRank

/-! # Strict non-dominance of actual projective evaluation incidence charts -/
@[expose] public noncomputable section
universe u
namespace ProjectiveEvaluationIncidence
variable (k A : Type u) [Field k] [CommRing A] [Algebra k A]
  {N : Type u} [Fintype N]

/-- The literal normalized coordinate makes all evaluation constraints independent
in the actual coefficient field of each component. -/
theorem trdeg_component_relative_bound (a : N → A) (n : ℕ) (j : N) (hj : a j = 1)
    (P : Ideal (Ring A a n)) [P.IsPrime] :
    let E := FractionRing (Ring A a n ⧸ P)
    let K := IncidenceCoefficientField.field k A E
    Algebra.trdeg K E + (n : Cardinal.{u}) ≤ (n * Fintype.card N : ℕ) := by
  let C := Ring A a n ⧸ P
  let E := FractionRing C
  let K := IncidenceCoefficientField.field k A E
  let := IncidenceCoefficientField.algebra k A E
  have hf := LinearIncidence.trdeg_fractionField_add_card_le A K C E
    (matrix A a n) (mapped_matrix_surjective A K a n j hj)
    (Ideal.Quotient.mkₐ A P) (Ideal.Quotient.mkₐ_surjective A P)
  simpa only [Fintype.card_fin, Fintype.card_prod] using hf

/-- Actual component fraction fields lose one parameter when the number of
linear forms exceeds the original chart's transcendence-degree bound. -/
theorem trdeg_component_add_one_le (a : N → A) (n : ℕ) (j : N) (hj : a j = 1)
    (hd : Algebra.trdeg k A + 1 ≤ (n : Cardinal.{u}))
    (P : Ideal (Ring A a n)) [P.IsPrime] :
    Algebra.trdeg k (Ring A a n ⧸ P) + 1 ≤ (n * Fintype.card N : ℕ) := by
  let C := Ring A a n ⧸ P
  let E := FractionRing C
  let K := IncidenceCoefficientField.field k A E
  have hK : Algebra.trdeg k K + 1 ≤ (n : Cardinal.{u}) :=
    (add_le_add (IncidenceCoefficientField.trdeg_field_le k A E) le_rfl).trans hd
  have hf := trdeg_component_relative_bound k A a n j hj P
  have ht : Algebra.trdeg k E + 1 ≤ (n * Fintype.card N : ℕ) := by
    calc
      Algebra.trdeg k E + 1 =
          (Algebra.trdeg k K + 1) + Algebra.trdeg K E := by
        rw [← trdeg_add_eq k K (A := E)]
        ac_rfl
      _ ≤ (n : Cardinal.{u}) + Algebra.trdeg K E := add_le_add hK le_rfl
      _ = Algebra.trdeg K E + n := add_comm _ _
      _ ≤ _ := hf
  have hc : Algebra.trdeg k C ≤ Algebra.trdeg k E :=
    trdeg_le_of_injective (IsScalarTower.toAlgHom k C E) (IsFractionRing.injective C E)
  exact (add_le_add hc le_rfl).trans ht

/-- A genuine ground-field equation excludes all common zeros on this full chart,
including its original nilpotents and every field-valued point. -/
theorem exists_nonzero_parameter_relation (a : N → A) (n : ℕ) (j : N) (hj : a j = 1)
    (hd : Algebra.trdeg k A + 1 ≤ (n : Cardinal.{u})) :
    ∃ f : MvPolynomial (Fin n × N) k, f ≠ 0 ∧ parameterMap A k a n f = 0 := by
  apply Algebra.exists_nonzero_kernel_of_minimal_quotient_trdeg_lt
  intro P hP
  have : P.IsPrime := hP.isPrime
  have h := trdeg_component_add_one_le k A a n j hj hd P
  have hfin : Algebra.trdeg k (Ring A a n ⧸ P) < Cardinal.aleph0 :=
    (le_self_add.trans h).trans_lt Cardinal.natCast_lt_aleph0
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp hfin
  rw [hm] at h
  simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype,
    Cardinal.lift_natCast, Fintype.card_prod, Fintype.card_fin, hm] using
      Cardinal.natCast_add_one_le_iff.mp h

end ProjectiveEvaluationIncidence
