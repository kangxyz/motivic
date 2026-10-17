/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.LinearIncidenceBaseChange
public import Motivic.Aglib.RingTheory.AlgebraicIndependent.FractionImageTrdeg

/-! # Generic-component bounds for the actual linear evaluation incidence -/
@[expose] public noncomputable section
open MvPolynomial
universe u v
namespace LinearIncidence

/-- Independent rows lower the dimension of the full original linear quotient. -/
theorem trdeg_coordinateRing_add_card_le {K N : Type u} {Q : Type v} [Field K]
    [Fintype N] [Fintype Q] (M : Matrix Q N K)
    (hM : Function.Surjective M.mulVec) :
    Algebra.trdeg K (CoordinateRing M) + (Fintype.card Q : Cardinal.{u}) ≤
      Fintype.card N := by
  have h := Algebra.trdeg_adjoin_add_card_le_of_surjective_matrix M hM
    (coordinates M) (equations_hold M)
  rw [adjoin_coordinates_eq_top] at h
  have he := (Subalgebra.topEquiv :
    (⊤ : Subalgebra K (CoordinateRing M)) ≃ₐ[K] CoordinateRing M).trdeg_eq
  simpa only [he] using h

/-- The component fraction field is generated algebraically by the specialized
incidence image; this is derived from the original coordinate presentation. -/
theorem trdeg_fractionField_add_card_le
    (A K C E : Type u) [CommRing A] [Field K] [CommRing C] [IsDomain C] [Field E]
    [Algebra A K] [Algebra A C] [Algebra C E] [IsFractionRing C E]
    [Algebra A E] [Algebra K E] [IsScalarTower A K E] [IsScalarTower A C E]
    {N : Type u} {Q : Type v} [Fintype N] [Fintype Q] (M : Matrix Q N A)
    (hM : Function.Surjective (M.map (algebraMap A K)).mulVec)
    (q : CoordinateRing M →ₐ[A] C) (hq : Function.Surjective q) :
    Algebra.trdeg K E + (Fintype.card Q : Cardinal.{u}) ≤ Fintype.card N := by
  let h := (IsScalarTower.toAlgHom A C E).comp q
  let f := specialize A K E M h
  have ht : Algebra.trdeg K E ≤ Algebra.trdeg K
      (CoordinateRing (M.map (algebraMap A K))) := by
    apply f.trdeg_le_of_fractionRing_image_mem (C := C)
    intro c
    obtain ⟨c', rfl⟩ := hq c
    exact image_mem_specialize_range A K E M h c'
  exact (add_le_add ht le_rfl).trans (trdeg_coordinateRing_add_card_le _ hM)

end LinearIncidence
