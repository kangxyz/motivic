/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.FiniteBaseNeighborhood

/-! # Two original finite-boundary frames on one prescribed base neighborhood

Intended upstream module: `Aglib.AlgebraicGeometry.Modules.Invertible.Frames.CommonFiniteBase`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.CommonFrames`.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- Choose each frame once, then restrict both to one affine neighborhood inside the
prescribed old base open. The full finite schemes, including nilpotents, are retained. -/
theorem exists_common_affine_base_unitIso_of_isFinite
    {B₁ B₂ S : Scheme.{u}} (b₁ : B₁ ⟶ S) (b₂ : B₂ ⟶ S)
    [IsFinite b₁] [IsFinite b₂] (L₁ : LineBundle B₁) (L₂ : LineBundle B₂)
    (W : S.Opens) (x : S) (hx : x ∈ W) :
    ∃ (O : S.Opens) (_hO : IsAffineOpen O), x ∈ O ∧ O ≤ W ∧
      Nonempty (((Modules.restrictFunctor (b₁ ⁻¹ᵁ O).ι).obj L₁.val ≅
        SheafOfModules.unit (b₁ ⁻¹ᵁ O).toScheme.ringCatSheaf) ×
        ((Modules.restrictFunctor (b₂ ⁻¹ᵁ O).ι).obj L₂.val ≅
          SheafOfModules.unit (b₂ ⁻¹ᵁ O).toScheme.ringCatSheaf)) := by
  obtain ⟨U₁, hx₁, ⟨e₁⟩⟩ := exists_base_open_unitIso_of_isFinite b₁ x L₁
  obtain ⟨U₂, hx₂, ⟨e₂⟩⟩ := exists_base_open_unitIso_of_isFinite b₂ x L₂
  obtain ⟨O, hO, hxO, hsub⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ W ⊓ (U₁ ⊓ U₂) from ⟨hx, hx₁, hx₂⟩)
  refine ⟨O, hO, hxO, fun t ht => (hsub ht).1, ⟨⟨?_, ?_⟩⟩⟩
  · exact restrictUnitIsoOfLE L₁.val (fun t ht => (hsub ht).2.1) e₁
  · exact restrictUnitIsoOfLE L₂.val (fun t ht => (hsub ht).2.2) e₂

end AlgebraicGeometry.Scheme.Modules.Invertible
