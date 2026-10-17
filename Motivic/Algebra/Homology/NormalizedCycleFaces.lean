/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.SingularNormalizedCyclePaths

/-! # Every face of a positive-degree normalized cycle vanishes -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
open scoped Simplicial

universe u

namespace Motivic.SingularComplex

/-- In the actual normalized Moore complex, the zeroth face is its differential. -/
theorem normalized_zero_face (S : SimplicialObject AddCommGrpCat.{u}) (n : ℕ) :
    (inclusionOfMooreComplexMap S).f (n + 1) ≫ S.δ 0 =
      ((normalizedMooreComplex AddCommGrpCat).obj S).d (n + 1) n ≫
        (inclusionOfMooreComplexMap S).f n := by
  rw [normalizedMooreComplex_objD]
  simp only [inclusionOfMooreComplexMap_f]
  cases n <;> simp [NormalizedMooreComplex.objD]

/-- All faces of an actual normalized cycle vanish, including the zeroth face. -/
theorem normalized_cycle_faces (S : SimplicialObject AddCommGrpCat.{u}) (n : ℕ)
    (x : ((normalizedMooreComplex AddCommGrpCat).obj S).X (n + 1))
    (hx : ((normalizedMooreComplex AddCommGrpCat).obj S).d (n + 1) n x = 0)
    (i : Fin (n + 2)) :
    S.δ i ((inclusionOfMooreComplexMap S).f (n + 1) x) = 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have h := ConcreteCategory.congr_hom (normalized_zero_face S n) x
    change S.δ 0 ((inclusionOfMooreComplexMap S).f (n + 1) x) =
      (inclusionOfMooreComplexMap S).f n
        (((normalizedMooreComplex AddCommGrpCat).obj S).d (n + 1) n x) at h
    rw [hx, map_zero] at h
    exact h
  · exact ConcreteCategory.congr_hom
      (DoldKan.HigherFacesVanish.inclusionOfMooreComplexMap (X := S) n j (by omega)) x

end Motivic.SingularComplex
