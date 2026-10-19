/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.SingularComplex.Parameters
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy

/-!
# The simplex prism for singular chains

The ordinal cuts below are the geometric prism maps used for the endpoint
chain homotopy in MVW Lemma 2.18 and the weight-one acyclicity argument.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SingularComplex.Prism

/-- The ordinal map which separates the two ends of the `i`-th prism simplex. -/
def cut {n : ℕ} (i : Fin (n + 1)) : ⦋n + 1⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.mkHom
    ⟨fun j => if j.val ≤ i.val then 0 else 1, by
      intro a b hab
      dsimp only
      split_ifs <;> simp_all
      omega⟩

lemma cut_zero_face (n : ℕ) :
    SimplexCategory.δ (0 : Fin (n + 2)) ≫ cut (0 : Fin (n + 1)) =
      SimplexCategory.const ⦋n⦌ ⦋1⦌ 1 := by
  ext j
  simp [cut, SimplexCategory.δ, SimplexCategory.const, Fin.succAbove]

lemma cut_last_face (n : ℕ) :
    SimplexCategory.δ (Fin.last (n + 1)) ≫ cut (Fin.last n) =
      SimplexCategory.const ⦋n⦌ ⦋1⦌ 0 := by
  ext j
  simp [cut, SimplexCategory.δ, SimplexCategory.const, Fin.succAbove]
  omega

lemma cut_face_left {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) :
    SimplexCategory.δ i.castSucc ≫ cut j.succ = cut j := by
  ext a
  change (if (i.castSucc.succAbove a).val ≤ j.val + 1 then (0 : Fin 2) else 1).val =
    (if a.val ≤ j.val then (0 : Fin 2) else 1).val
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  rcases a with ⟨a, ha⟩
  dsimp [Fin.succAbove]
  split_ifs <;> simp_all <;> omega

lemma cut_face_middle {n : ℕ} (j : Fin (n + 1)) :
    SimplexCategory.δ j.castSucc.succ ≫ cut j.succ =
      SimplexCategory.δ j.castSucc.succ ≫ cut j.castSucc := by
  ext a
  change (if (j.castSucc.succ.succAbove a).val ≤ j.val + 1 then (0 : Fin 2) else 1).val =
    (if (j.castSucc.succ.succAbove a).val ≤ j.val then (0 : Fin 2) else 1).val
  rcases j with ⟨j, hj⟩
  rcases a with ⟨a, ha⟩
  dsimp [Fin.succAbove]
  split_ifs <;> simp_all <;> omega

lemma cut_face_right {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) :
    SimplexCategory.δ i.succ ≫ cut j.castSucc = cut j := by
  ext a
  change (if (i.succ.succAbove a).val ≤ j.val then (0 : Fin 2) else 1).val =
    (if a.val ≤ j.val then (0 : Fin 2) else 1).val
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  rcases a with ⟨a, ha⟩
  dsimp [Fin.succAbove]
  split_ifs <;> simp_all <;> omega

lemma cut_degeneracy_left {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    SimplexCategory.σ i.castSucc ≫ cut j = cut j.succ := by
  ext a
  change (if (i.castSucc.predAbove a).val ≤ j.val then (0 : Fin 2) else 1).val =
    (if a.val ≤ j.val + 1 then (0 : Fin 2) else 1).val
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  rcases a with ⟨a, ha⟩
  dsimp [Fin.predAbove]
  split_ifs <;> simp_all [Fin.pred, Fin.castPred]
  all_goals
    simp_all only [Fin.lt_def]
    omega

lemma cut_degeneracy_right {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    SimplexCategory.σ i.succ ≫ cut j = cut j.castSucc := by
  ext a
  change (if (i.succ.predAbove a).val ≤ j.val then (0 : Fin 2) else 1).val =
    (if a.val ≤ j.val then (0 : Fin 2) else 1).val
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  rcases a with ⟨a, ha⟩
  dsimp [Fin.predAbove]
  split_ifs <;> simp_all [Fin.pred, Fin.castPred]
  all_goals
    simp_all only [Fin.lt_def]
    omega

end CategoryTheory.SingularComplex.Prism
