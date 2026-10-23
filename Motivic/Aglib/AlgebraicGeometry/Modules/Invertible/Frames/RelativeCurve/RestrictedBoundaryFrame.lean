/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.LocalAffineBaseFrame
public import Aglib.AlgebraicGeometry.IdealSheaf.Restriction
/-! # Literal ideal and canonical functional after restricting a boundary graph -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {D X : Scheme.{u}} (i : D ⟶ X) (U : X.Opens)

/-- An actual local frame becomes a frame of the original restricted closed subscheme. -/
def restrictedIdealFrame
    (e : (idealModule i).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    SheafOfModules.unit U.toScheme.ringCatSheaf ≅ idealModule (i ∣_ U) :=
  e.symm ≪≫ idealRestrictionIso i U

@[reassoc]
theorem restrictedIdealFrame_inclusion
    (e : (idealModule i).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (restrictedIdealFrame i U e).hom ≫ idealInclusion (i ∣_ U) =
      e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (idealInclusion i) ≫
        (restrictUnitIso U.ι).hom := by
  simp only [restrictedIdealFrame, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [idealRestrictionIso_hom_inclusion i U]
/-- The finite-boundary construction yields a frame of the actual restricted graph
ideal on an affine source neighborhood, retaining the entire boundary over one base open. -/
theorem exists_affine_restrictedBoundaryGraphFrame
    {S Y Z : Scheme.{u}} (q : Y ⟶ S) [IsSeparated q]
    [SmoothOfRelativeDimension 1 q] [IsAffine Y]
    (z : Z ⟶ Y) [IsFinite (z ≫ q)] (y : Y) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ y ∈ U ∧ ∃ V : S.Opens, q y ∈ V ∧
      (∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U) ∧
      Nonempty (SheafOfModules.unit
        ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).toScheme.ringCatSheaf ≅
        idealModule (boundaryGraphTarget q z ∣_ (pullback.fst q (z ≫ q)) ⁻¹ᵁ U)) := by
  obtain ⟨U, hU, hy, V, hv, hz, ⟨e⟩⟩ :=
    exists_affine_relativeBoundaryFrame_over_base_neighborhood q z y
  exact ⟨U, hU, hy, V, hv, hz, ⟨restrictedIdealFrame _ _ e⟩⟩
end AlgebraicGeometry.Scheme.Hom
