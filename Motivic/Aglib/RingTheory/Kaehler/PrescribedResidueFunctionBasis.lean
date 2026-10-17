/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Kaehler.ResidueFunctionBasis
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

/-- A prescribed function with nonzero residue differential remains one of the
original functions in a finite residue differential basis. -/
theorem exists_residue_basis_original_functions_containing
    (k : Type u) (R : Type v) (K : Type w)
    [CommRing k] [CommRing R] [Field K] [Algebra k R] [Algebra R K]
    [Algebra.EssFiniteType k R] (f : R)
    (hf : (1 ⊗ₜ[R] D k R f : K ⊗[R] Ω[R⁄k]) ≠ 0) :
    ∃ (s : Set R), s.Finite ∧ f ∈ s ∧
      ∃ b : Basis s K (K ⊗[R] Ω[R⁄k]), ∀ j, b j = 1 ⊗ₜ[R] D k R j := by
  let v : R → K ⊗[R] Ω[R⁄k] := fun x => 1 ⊗ₜ[R] D k R x
  have hv : Submodule.span K (Set.range v) = ⊤ :=
    span_residue_original_differentials k R K
  have hli : LinearIndepOn K v {f} := (linearIndepOn_singleton_iff K).mpr hf
  let s := hli.extend (Set.subset_univ {f})
  have hsp : Submodule.span K (Set.range (fun j : s => v j)) = ⊤ := by
    rw [show Set.range (fun j : s => v j) = v '' s from by
      ext z
      simp only [Set.mem_range, Set.mem_image, Subtype.exists, exists_prop]]
    rw [hli.span_image_extend_eq_span_image, Set.image_univ, hv]
  let b : Basis s K (K ⊗[R] Ω[R⁄k]) := Basis.mk (hli.linearIndepOn_extend _) hsp.ge
  have : Finite s := Module.Finite.finite_basis b
  exact ⟨s, Set.toFinite s, hli.subset_extend _ (Set.mem_singleton f),
    b, fun _ => Basis.mk_apply _ _ _⟩

end KaehlerDifferential
