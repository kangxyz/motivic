/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Kaehler.PrincipalConormal
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # A local differential basis containing the original divisor equation -/

@[expose] public noncomputable section

open Module TensorProduct KaehlerDifferential

universe u v w

namespace IsLocalRing

/-- A specified generator nonzero in the residue fiber can be retained in a
basis selected from the original generating family of a finite flat module. -/
theorem exists_basis_subfamily_containing
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M]
    {ι : Type w} (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤)
    (i : ι) (hi : (1 ⊗ₜ[R] v i : ResidueField R ⊗[R] M) ≠ 0) :
    ∃ (s : Set ι), i ∈ s ∧ ∃ b : Basis s R M, ∀ j, b j = v j := by
  let K := ResidueField R
  let w : ι → K ⊗[R] M := fun j ↦ 1 ⊗ₜ v j
  have hw : Submodule.span K (Set.range w) = ⊤ := by
    apply (Submodule.restrictScalars_injective R)
    rw [Submodule.restrictScalars_span R K Ideal.Quotient.mk_surjective]
    change Submodule.span R (Set.range ((TensorProduct.mk R K M 1) ∘ v)) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, hv, Submodule.map_top,
      LinearMap.range_eq_top]
    exact TensorProduct.mk_surjective R M K Ideal.Quotient.mk_surjective
  have hli : LinearIndepOn K w {i} := (linearIndepOn_singleton_iff K).mpr hi
  let s := hli.extend (Set.subset_univ {i})
  have hs : i ∈ s := hli.subset_extend _ (by simp)
  have hsp : Submodule.span K (Set.range (fun j : s ↦ w j)) = ⊤ := by
    rw [show Set.range (fun j : s ↦ w j) = w '' s from by
      ext z
      simp only [Set.mem_range, Set.mem_image, Subtype.exists, exists_prop]]
    rw [hli.span_image_extend_eq_span_image, Set.image_univ, hw]
  let bK : Basis s K (K ⊗[R] M) := Basis.mk
    (hli.linearIndepOn_extend _) hsp.ge
  have hbK (j : s) : bK j = 1 ⊗ₜ v j := Basis.mk_apply _ _ _
  have hlift : LinearIndependent R (fun j : s ↦ v j) :=
    IsLocalRing.linearIndependent_of_flat _ (by
      simpa only [Function.comp_def, TensorProduct.mk_apply, ← hbK] using bK.linearIndependent)
  refine ⟨s, hs, Basis.mk hlift ?_, fun _ ↦ Basis.mk_apply _ _ _⟩
  exact (IsLocalRing.span_eq_top_of_tmul_eq_basis _ bK (fun j ↦ (hbK j).symm)).ge

end IsLocalRing

namespace Algebra.FormallySmooth

/-- At a local ring the actual regular divisor equation belongs to a basis of
actual differentials of ring elements. The chosen equation is not replaced. -/
theorem exists_differential_basis_containing_regular_generator
    (k : Type u) (R : Type v) [CommRing k] [CommRing R] [Algebra k R]
    [IsLocalRing R] [EssFiniteType k R] [FormallySmooth k R]
    (t : R) (ht : IsRegular t) (htm : t ∈ IsLocalRing.maximalIdeal R)
    [FormallySmooth k (R ⧸ Ideal.span {t})] :
    ∃ (s : Set R), t ∈ s ∧ ∃ b : Basis s R Ω[R⁄k], ∀ j, b j = D k R j := by
  apply IsLocalRing.exists_basis_subfamily_containing R Ω[R⁄k] (D k R)
    (span_range_derivation k R) t
  apply tensor_differential_ne_zero_of_regular_quotient k R t ht
  exact (IsLocalRing.residue_eq_zero_iff t).mpr htm

end Algebra.FormallySmooth
