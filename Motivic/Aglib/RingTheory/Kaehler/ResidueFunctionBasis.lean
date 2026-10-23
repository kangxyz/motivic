/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Residue cotangent bases from actual affine functions

The basis is selected from differentials of elements of the original ring.
There is no rational-point, separability, or chosen smooth-chart assumption.
-/
@[expose] public noncomputable section
open Module TensorProduct KaehlerDifferential
universe u v w
namespace KaehlerDifferential

/-- The actual differentials of original functions span every residue cotangent
fiber, even when the residue field differs from the ground field. -/
theorem span_residue_original_differentials
    (k : Type u) (R : Type v) (K : Type w)
    [CommRing k] [CommRing R] [Field K] [Algebra k R] [Algebra R K] :
    Submodule.span K (Set.range (fun x : R => (1 ⊗ₜ[R] D k R x : K ⊗[R] Ω[R⁄k]))) = ⊤ := by
  have h := congrArg (Submodule.baseChange K) (span_range_derivation k R)
  simpa only [Submodule.baseChange_span, Submodule.baseChange_top,
    ← Set.range_comp, Function.comp_def, TensorProduct.mk_apply] using h

/-- A finite basis of the residue cotangent fiber can be chosen among actual
original affine functions. This supplies genuine starting differential data. -/
theorem exists_residue_basis_original_functions
    (k : Type u) (R : Type v) (K : Type w)
    [CommRing k] [CommRing R] [Field K] [Algebra k R] [Algebra R K]
    [Algebra.EssFiniteType k R] :
    ∃ (s : Set R), s.Finite ∧
      ∃ b : Basis s K (K ⊗[R] Ω[R⁄k]), ∀ j, b j = 1 ⊗ₜ[R] D k R j := by
  let v : R → K ⊗[R] Ω[R⁄k] := fun x => 1 ⊗ₜ[R] D k R x
  have hv : Submodule.span K (Set.range v) = ⊤ :=
    span_residue_original_differentials k R K
  have hli : LinearIndepOn K v ∅ := linearIndepOn_empty K v
  let s := hli.extend (Set.subset_univ ∅)
  have hsp : Submodule.span K (Set.range (fun j : s => v j)) = ⊤ := by
    rw [show Set.range (fun j : s => v j) = v '' s from by
      ext z
      simp only [Set.mem_range, Set.mem_image, Subtype.exists, exists_prop]]
    rw [hli.span_image_extend_eq_span_image, Set.image_univ, hv]
  let b : Basis s K (K ⊗[R] Ω[R⁄k]) := Basis.mk (hli.linearIndepOn_extend _) hsp.ge
  have : Finite s := Module.Finite.finite_basis b
  exact ⟨s, Set.toFinite s, b, fun _ => Basis.mk_apply _ _ _⟩

/-- A prescribed residue dimension gives an indexed basis of actual function
values, ready for simultaneous linear-coordinate selection. -/
theorem exists_residue_basis_fin_original_functions
    (k : Type u) (R : Type v) (K : Type w)
    [CommRing k] [CommRing R] [Field K] [Algebra k R] [Algebra R K]
    [Algebra.EssFiniteType k R] (d : ℕ)
    (hd : Module.finrank K (K ⊗[R] Ω[R⁄k]) = d) :
    ∃ (g : Fin d → R) (b : Basis (Fin d) K (K ⊗[R] Ω[R⁄k])),
      ∀ j, b j = 1 ⊗ₜ[R] D k R (g j) := by
  obtain ⟨s, hs, b, hb⟩ := exists_residue_basis_original_functions k R K
  let := hs.fintype
  have hc : Fintype.card s = d := (Module.finrank_eq_card_basis b).symm.trans hd
  let e : s ≃ Fin d := Fintype.equivFinOfCardEq hc
  exact ⟨fun j => (e.symm j).val, b.reindex e, fun j => by
    simpa only [Basis.reindex_apply] using hb (e.symm j)⟩

end KaehlerDifferential
