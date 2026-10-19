/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.FieldEvaluation

/-!
# Consumers of field lifting and exact field evaluation

These tests check the residue-field interpretation and abelian exactness before
the additional étale condition defining the Nisnevich topology is imposed.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Nisnevich

universe u

example (X : Scheme.{u}) (R : Presieve X) :
    R ∈ fieldLiftingPrecoverage X ↔ IsResidueFieldLifting R :=
  mem_fieldLiftingPrecoverage_iff_residueField

example (K : Type u) [Field K] :
    (⊥ : Sieve (Spec (.of K))) ∉ fieldLiftingTopology _ := by
  intro h
  have ht := fieldLifting_covering_sieve_eq_top K h
  have hi : (⊥ : Sieve (Spec (.of K))) (𝟙 _) := by rw [ht]; trivial
  exact hi

example (K : Type u) [Field K]
    {F G : Sheaf fieldLiftingTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op (Spec (.of K)))) :=
  surjective_app_of_epi_of_le fieldLiftingTopology le_rfl K φ

example (K : Type u) [Field K]
    (S : ShortComplex (Sheaf fieldLiftingTopology AddCommGrpCat.{u + 1})) (hS : S.Exact) :
    (S.map (fieldEvaluation fieldLiftingTopology K)).Exact :=
  exact_map_fieldEvaluation fieldLiftingTopology le_rfl K S hS

#print axioms mem_fieldLiftingPrecoverage_iff_residueField
#print axioms fieldLifting_covering_sieve_eq_top
#print axioms surjective_app_of_epi_of_le
#print axioms exact_map_fieldEvaluation
