module

public import Motivic.Aglib.RingTheory.AlgebraicIndependent.LinearRelationsTrdeg
public import Mathlib.Tactic.FinCases
public import Lean.Util.CollectAxioms

/-! # Direct consumers of the linear-relations transcendence bound

These tests include a genuine relation between two possibly transcendental
coordinates, the zero-coordinate endpoint, and the intrinsic kernel formula.
-/

@[expose] public noncomputable section

open scoped BigOperators

universe u v

namespace Motivic.MotivicTest.LinearRelationsTrdeg

variable {F E : Type u} [Field F] [CommRing E] [Algebra F E]

/-- The coefficient vector `(c, -c)` gives a nonzero relation between repeated
coordinates. -/
def repeatedCoordinateRelation : (Fin 1 → F) →ₗ[F] (Fin 2 → F) where
  toFun c := ![c 0, -c 0]
  map_add' c d := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' a c := by ext i; fin_cases i <;> simp

/-- The repeated-coordinate relation has rank one. -/
theorem repeatedCoordinateRelation_injective :
    Function.Injective (repeatedCoordinateRelation (F := F)) := by
  intro c d h
  have h0 := congrFun h 0
  ext i
  fin_cases i
  simpa [repeatedCoordinateRelation] using h0

/-- The actual generated algebra of `(a,a)` has at most one transcendental
parameter, for arbitrary `a`, not only algebraic elements. -/
theorem repeatedCoordinate_bound (a : E) :
    Algebra.trdeg F (Algebra.adjoin F (Set.range (![a, a] : Fin 2 → E))) + 1 ≤
      (2 : Cardinal.{u}) := by
  have h := Algebra.trdeg_adjoin_add_card_le_of_injective_linear_relations
    (![a, a] : Fin 2 → E) (repeatedCoordinateRelation (F := F))
    repeatedCoordinateRelation_injective (fun c => by
      simp [Fintype.linearCombination_apply, Fin.sum_univ_succ,
        repeatedCoordinateRelation])
  simpa using h

/-- With every coordinate zero, the identity gives as many independent
relations as there are coordinates. -/
theorem allZeroCoordinates_bound {N : Type v} [Fintype N] :
    Algebra.trdeg F (Algebra.adjoin F (Set.range (fun _ : N => (0 : E)))) +
      (Fintype.card N : Cardinal.{u}) ≤ Fintype.card N := by
  exact Algebra.trdeg_adjoin_add_card_le_of_injective_linear_relations
    (fun _ : N => (0 : E)) (LinearMap.id : (N → F) →ₗ[F] (N → F))
    Function.injective_id (fun c => by simp [Fintype.linearCombination_apply])

/-- The intrinsic formulation computes the actual kernel dimension and needs
no externally supplied transcendence-degree estimate. -/
theorem actualKernel_bound {N : Type v} [Fintype N] (x : N → E) :
    Algebra.trdeg F (Algebra.adjoin F (Set.range x)) +
      (Module.finrank F (LinearMap.ker (Fintype.linearCombination F x)) : Cardinal.{u}) ≤
        Fintype.card N :=
  Algebra.trdeg_adjoin_add_finrank_ker_linearCombination_le x

/-- A literal one-by-two full-row-rank relation matrix. -/
def repeatedCoordinateMatrix : Matrix (Fin 1) (Fin 2) F :=
  fun _ => ![1, -1]

/-- Its row map is surjective in every characteristic. -/
theorem repeatedCoordinateMatrix_surjective :
    Function.Surjective (repeatedCoordinateMatrix (F := F)).mulVec := by
  intro y
  refine ⟨![y 0, 0], ?_⟩
  ext i
  fin_cases i
  simp [repeatedCoordinateMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The matrix interface uses its actual scalar-extended equations, not a
supplied kernel dimension or transcendence-degree bound. -/
theorem repeatedCoordinate_matrix_bound (a : E) :
    Algebra.trdeg F (Algebra.adjoin F (Set.range (![a, a] : Fin 2 → E))) + 1 ≤
      (2 : Cardinal.{u}) := by
  have hx : ((repeatedCoordinateMatrix (F := F)).map (algebraMap F E)).mulVec
      (![a, a] : Fin 2 → E) = 0 := by
    ext i
    fin_cases i
    simp [repeatedCoordinateMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  simpa using Algebra.trdeg_adjoin_add_card_le_of_surjective_matrix
    (repeatedCoordinateMatrix (F := F)) repeatedCoordinateMatrix_surjective
    (![a, a] : Fin 2 → E) hx

open Lean in
run_cmd do
  for name in #[``Algebra.trdeg_adjoin_submodule_le_finrank,
      ``Algebra.trdeg_adjoin_add_finrank_ker_linearCombination_le,
      ``Algebra.trdeg_adjoin_add_card_le_of_injective_linear_relations,
      ``Algebra.trdeg_adjoin_add_card_le_of_surjective_matrix,
      ``repeatedCoordinateRelation, ``repeatedCoordinateRelation_injective,
      ``repeatedCoordinate_bound, ``allZeroCoordinates_bound, ``actualKernel_bound,
      ``repeatedCoordinateMatrix, ``repeatedCoordinateMatrix_surjective,
      ``repeatedCoordinate_matrix_bound] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Linear-relations transcendence bounds use only standard Lean foundations."

end Motivic.MotivicTest.LinearRelationsTrdeg
