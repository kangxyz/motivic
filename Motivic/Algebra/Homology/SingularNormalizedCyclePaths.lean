/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.SingularComplexEndpoints
public import Motivic.Algebra.Homology.SingularComplexNormalization
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Nonlinear cycle paths and all-degree singular acyclicity

A path can be chosen separately for each normalized cycle. It need not be a
homomorphism. The actual prism converts each such path into a boundary, and
the established normalization comparison transfers the result to all chains.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Motivic.SingularComplex

/-- A chain map whose every cycle is sent to a boundary is zero on homology. -/
theorem homologyMap_eq_zero_of_cycle_boundaries
    {K L : ChainComplex AddCommGrpCat.{w} ℕ} (α : K ⟶ L) (n : ℕ)
    (h : ∀ x : K.X n, (∀ m, K.d n m x = 0) →
      ∃ y : L.X (n + 1), L.d (n + 1) n y = α.f n x) :
    HomologicalComplex.homologyMap α n = 0 := by
  apply (cancel_epi (K.homologyπ n)).mp
  rw [HomologicalComplex.homologyπ_naturality, comp_zero]
  ext x
  obtain ⟨y, hy⟩ := h (K.iCycles n x) (fun m =>
    ConcreteCategory.congr_hom (K.iCycles_d n m) x)
  have hc : HomologicalComplex.cyclesMap α n x = L.toCycles (n + 1) n y := by
    apply (AddCommGrpCat.mono_iff_injective (L.iCycles n)).mp inferInstance
    have hl := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i α n) x
    have hr := ConcreteCategory.congr_hom (L.toCycles_i (n + 1) n) y
    exact hl.trans (hy.symm.trans hr.symm)
  change L.homologyπ n (HomologicalComplex.cyclesMap α n x) = 0
  rw [hc, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
  rfl

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]

/-- All normalized cycles admitting genuine zero-to-cycle prism paths imply
acyclicity of the original unnormalized singular complex, in every degree. -/
theorem isZero_homology_of_normalized_cycle_paths
    (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ)
    (h : ∀ x : (normalizedObj Δ P).X n,
      (∀ m, (normalizedObj Δ P).d n m x = 0) →
      ∃ y : (obj (Prism.cylinder Δ) P).X n,
        (∀ m, (obj (Prism.cylinder Δ) P).d n m y = 0) ∧
        (geometryMap (Prism.endpoint Δ 0) P).f n y = 0 ∧
        (geometryMap (Prism.endpoint Δ 1) P).f n y =
          ((normalizedInclusion Δ).app P).f n x) :
    IsZero ((obj Δ P).homology n) := by
  have hz : HomologicalComplex.homologyMap ((normalizedInclusion Δ).app P) n = 0 := by
    apply homologyMap_eq_zero_of_cycle_boundaries
    intro x hx
    obtain ⟨y, hy, h0, h1⟩ := h x hx
    refine ⟨-((Prism.endpointHomotopy Δ P).hom n (n + 1) y), ?_⟩
    exact (Prism.boundary_of_cycle_path (Prism.endpointHomotopy Δ P) n y hy h0).trans h1
  have hi : IsIso (HomologicalComplex.homologyMap ((normalizedInclusion Δ).app P) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance
  exact (IsZero.iff_id_eq_zero _).mpr (by
    change 𝟙 (((functor Δ).obj P).homology n) = 0
    rw [← IsIso.inv_hom_id (HomologicalComplex.homologyMap ((normalizedInclusion Δ).app P) n),
       ]
    simp only [hz, comp_zero])

end Motivic.SingularComplex
