/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.NormalizedMovingPointChart
public import Mathlib.Data.Fintype.Card

/-! # Actual points and free-coordinate count of moving incidence charts -/
@[expose] public noncomputable section
namespace QuadraticIncidence.MovingPointChart
universe u
variable (B : Type u) [CommRing B] (d : ℕ) (i₀ : Fin d)

/-- There are exactly `d-1` free normalized weight coordinates. -/
theorem card_weightIndex : Fintype.card (WeightIndex d i₀) = d - 1 := by
  simp [WeightIndex, Fintype.card_subtype_compl]

/-- Every off-diagonal field point with specified weights evaluates the literal
localized chart; invertibility follows from the original coordinate difference. -/
def evaluate (t : B) (K : Type u) [Field K] [Algebra B K]
    (w : Fin d → K) (ht : algebraMap B K t ≠ 0) : Ring B d i₀ t →ₐ[B] K :=
  IsLocalization.Away.liftAlgHom (MvPolynomial.C t : PolynomialRing B d i₀)
    (f := MvPolynomial.aeval (fun i : WeightIndex d i₀ => w i.val))
    (by simpa using (isUnit_iff_ne_zero.mpr ht))

/-- The evaluation retains every original normalized weight, not just its span. -/
@[simp]
theorem evaluate_weight (t : B) (K : Type u) [Field K] [Algebra B K]
    (w : Fin d → K) (ht : algebraMap B K t ≠ 0) (hw : w i₀ = 1) (i : Fin d) :
    evaluate B d i₀ t K w ht (weight B d i₀ t i) = w i := by
  by_cases hi : i = i₀
  · subst i
    simp [hw]
  · simp [weight, hi, evaluate, IsLocalization.Away.liftAlgHom_apply]

end QuadraticIncidence.MovingPointChart
