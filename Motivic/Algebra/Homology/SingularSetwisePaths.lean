/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.NormalizedCycleFaces

/-! # Face-compatible nonlinear paths kill all singular homology -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
open scoped Simplicial

universe u v w

namespace Motivic.SingularComplex

variable {C : Type u} [Category.{v} C]

/-- A chain with every face zero is a cycle for the alternating differential. -/
theorem cycle_of_faces_zero (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (n : ℕ) (x : (obj Δ P).X n)
    (h : ∀ m (e : n = m + 1) (i : Fin (m + 2)),
      P.map (Δ.δ i).op (e ▸ x) = 0) :
    ∀ m, (obj Δ P).d n m x = 0 := by
  intro m
  by_cases e : n = m + 1
  · subst n
    rw [obj_d]
    let ev : (((obj Δ P).X (m + 1)) ⟶ (obj Δ P).X m) →+ (obj Δ P).X m :=
      (AddMonoidHom.eval x).comp AddCommGrpCat.homAddEquiv.toAddMonoidHom
    change ev (∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • P.map (Δ.δ i).op) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    change (((-1 : ℤ) ^ (i : ℕ) • P.map (Δ.δ i).op).hom) x = 0
    simp only [AddCommGrpCat.hom_zsmul, AddMonoidHom.zsmul_apply, h m rfl i, smul_zero]
  · rw [(obj Δ P).shape n m (by simpa [eq_comm] using e)]
    rfl

variable [HasBinaryProducts C]

/-- A face-compatible choice of paths, preserving zero and joining zero to each
chain, contracts all normalized cycles. No additivity of the chosen paths is required. -/
theorem isZero_homology_of_setwise_paths
    (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (path : ∀ n, (obj Δ P).X n → (obj (Prism.cylinder Δ) P).X n)
    (path_zero : ∀ n, path n 0 = 0)
    (path_face : ∀ n (i : Fin (n + 2)) (x : (obj Δ P).X (n + 1)),
      P.map ((Prism.cylinder Δ).δ i).op (path (n + 1) x) =
        path n (P.map (Δ.δ i).op x))
    (path_start : ∀ n x, (geometryMap (Prism.endpoint Δ 0) P).f n (path n x) = 0)
    (path_end : ∀ n x, (geometryMap (Prism.endpoint Δ 1) P).f n (path n x) = x)
    (n : ℕ) : IsZero ((obj Δ P).homology n) := by
  apply isZero_homology_of_normalized_cycle_paths
  intro x hx
  let z := ((normalizedInclusion Δ).app P).f n x
  refine ⟨path n z, ?_, path_start n z, path_end n z⟩
  apply cycle_of_faces_zero
  intro m e i
  subst n
  rw [path_face]
  have hf : P.map (Δ.δ i).op z = 0 :=
    normalized_cycle_faces (simplicial Δ P) m x (hx m) i
  rw [hf, path_zero]

end Motivic.SingularComplex
