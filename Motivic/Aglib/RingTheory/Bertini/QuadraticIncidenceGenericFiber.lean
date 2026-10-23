/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceDimension
public import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceSpecializationRange
public import Motivic.Aglib.RingTheory.AlgebraicIndependent.FractionImageTrdeg
public import Motivic.Aglib.RingTheory.Kaehler.SmoothCotangentTrdeg

/-! # The actual generic-field bound for a quadratic incidence component

The component is a genuine quotient of the original incidence ring. Its fraction
field receives the intermediate-coefficient incidence ring by the canonical
specialization map. Original coordinate generation, rather than an assumed
algebraicity property, transfers the incidence bound to that fraction field.
-/
@[expose] public noncomputable section
open Module TensorProduct KaehlerDifferential
universe u
namespace QuadraticIncidence
variable (k R A K C E : Type u) [Field k] [CommRing R] [IsDomain R]
  [CommRing A] [Field K] [CommRing C] [IsDomain C] [Field E]
  [Algebra k R] [Algebra R A] [Algebra R K] [Algebra A K]
  [Algebra A C] [Algebra C E] [IsFractionRing C E]
  [Algebra R E] [Algebra A E] [Algebra K E]
  [IsScalarTower R A E] [IsScalarTower R K E]
  [IsScalarTower A K E] [IsScalarTower A C E] [Algebra.Smooth k R]
  {σ : Type u} [Fintype σ]

/-- For an actual domain quotient, the normalized bad-fiber equations remove
`2d+1` transcendental parameters even after passing to its fraction field.
The cotangent rank is derived from smoothness and the original dimension. -/
theorem trdeg_fractionField_add_constraints_le
    (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (a : σ → A) (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (w : Fin d → A) (i₀ : Fin d) (hw : w i₀ = 1)
    (hab : algebraMap A K ∘ a ≠ fun i => algebraMap R K (g i))
    (q : CoordinateRing k R A g a d w →ₐ[A] C) (hq : Function.Surjective q) :
    Algebra.trdeg K E + ((2 * d + 1 : ℕ) : Cardinal.{u}) ≤
      (d * Fintype.card (Exponent σ) : ℕ) := by
  let h := (IsScalarTower.toAlgHom A C E).comp q
  let f := specialize k R A K E g a d w h
  have ht : Algebra.trdeg K E ≤
      Algebra.trdeg K (CoordinateRing k R K g (algebraMap A K ∘ a) d
        (algebraMap A K ∘ w)) := by
    apply f.trdeg_le_of_fractionRing_image_mem (C := C)
    intro c
    obtain ⟨c', rfl⟩ := hq c
    exact image_mem_specialize_range k R A K E g a d w h c'
  have hr : Module.finrank K (K ⊗[R] Ω[R⁄k]) = d + 1 := by
    rw [Algebra.cotangent_finrank_eq_trdeg_toNat k R K, hd]
    simp
  have hw' : (algebraMap A K ∘ w) i₀ = 1 := by simp [hw]
  exact (add_le_add ht le_rfl).trans
    (trdeg_coordinateRing_add_constraints_le k R K g hg (algebraMap A K ∘ a)
      hab d hr (algebraMap A K ∘ w) i₀ hw')

/-- A coefficient-field bound gives the strict dimension drop for the actual
component fraction field. The coefficient bound is the separate moving-point
and normalized-weight chart calculation, not a bound on the incidence ring. -/
theorem trdeg_fractionField_add_one_le
    [Algebra k K] [Algebra k E] [IsScalarTower k K E]
    (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (a : σ → A) (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (w : Fin d → A) (i₀ : Fin d) (hw : w i₀ = 1)
    (hab : algebraMap A K ∘ a ≠ fun i => algebraMap R K (g i))
    (q : CoordinateRing k R A g a d w →ₐ[A] C) (hq : Function.Surjective q)
    (hK : Algebra.trdeg k K ≤ (2 * d : ℕ)) :
    Algebra.trdeg k E + 1 ≤ (d * Fintype.card (Exponent σ) : ℕ) := by
  have hf := trdeg_fractionField_add_constraints_le k R A K C E
    g hg a d hd w i₀ hw hab q hq
  calc
    Algebra.trdeg k E + 1 =
        (Algebra.trdeg k K + Algebra.trdeg K E) + 1 := by
      rw [trdeg_add_eq k K]
    _ ≤ ((2 * d : ℕ) : Cardinal.{u}) + Algebra.trdeg K E + 1 :=
      add_le_add (add_le_add hK le_rfl) le_rfl
    _ = Algebra.trdeg K E + ((2 * d + 1 : ℕ) : Cardinal.{u}) := by
      rw [Nat.cast_add, Nat.cast_one]
      ac_rfl
    _ ≤ _ := hf

end QuadraticIncidence
