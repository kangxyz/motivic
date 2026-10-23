/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.ProjectiveIncidenceAlgebra

/-! # Dimension bound for the actual projective-module incidence quotient -/
@[expose] public noncomputable section
open Module LinearMap
universe u
namespace ProjectiveIncidence
variable {K V N : Type u} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V] [Fintype N]

/-- Independent original coefficient vectors lower the transcendence degree of
 the literal full quotient by the dimension of the actual equation module. -/
theorem trdeg_coordinateRing_add_finrank_le (v : N → V)
    (hv : Submodule.span K (Set.range v) = ⊤) :
    Algebra.trdeg K (CoordinateRing (R := K) v) + (Module.finrank K V : Cardinal.{u}) ≤
      Fintype.card N := by
  classical
  let b := Module.finBasis K V
  let A : Matrix (Fin (Module.finrank K V)) N K := fun i n => b.repr (v n) i
  have hLC : Function.Surjective (Fintype.linearCombination K v) := by
    apply LinearMap.range_eq_top.mp
    rw [Fintype.range_linearCombination, hv]
  have hA : Function.Surjective A.mulVec := by
    have hmap : A.mulVec = b.equivFun ∘ Fintype.linearCombination K v := by
      funext c
      ext i
      simp [A, Matrix.mulVec, dotProduct, Fintype.linearCombination_apply,
        Basis.equivFun_apply, mul_comm]
    rw [hmap]
    exact b.equivFun.surjective.comp hLC
  let x := LinearIncidence.coordinates (coefficientMatrix (R := K) v)
  have hx : (A.map (algebraMap K (CoordinateRing (R := K) v))).mulVec x = 0 := by
    ext i
    have h := congrFun (LinearIncidence.equations_hold (coefficientMatrix (R := K) v))
      (b.coord i)
    simpa [A, x, coefficientMatrix, Matrix.mulVec, dotProduct,
      Basis.coord_apply, Matrix.map_apply] using! h
  have h := Algebra.trdeg_adjoin_add_card_le_of_surjective_matrix A hA x hx
  rw [LinearIncidence.adjoin_coordinates_eq_top] at h
  have he := (Subalgebra.topEquiv :
    (⊤ : Subalgebra K (CoordinateRing (R := K) v)) ≃ₐ[K] CoordinateRing (R := K) v).trdeg_eq
  simpa only [he, Fintype.card_fin] using h

end ProjectiveIncidence
