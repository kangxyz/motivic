/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Sections.GlobalUnitPair
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Basic
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom

/-! The native Serre boundary map is exactly the adjoint of actual tensor pullback. -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph
/-- The whole-boundary section map uses the canonical tensor pullback, literally. -/
theorem boundaryRestriction_eq_adjoint {Z C : Scheme.{u}}
    (i : Z ⟶ C) [IsClosedImmersion i] (L M : C.Modules) :
    boundaryRestriction i L M =
      (pullbackPushforwardAdjunction i).homEquiv _ _ (pullbackTensorMap i L M) := by
  rw [pullbackTensorMap_adjoint]
  unfold boundaryRestriction
  rw [closedImmersionProjectionFormulaIso_hom]
  unfold projectionFormulaMap
  change tensorSheafMap C (𝟙 L) ((pullbackPushforwardAdjunction i).unit.app M) ≫
    tensorSheafMap C ((pullbackPushforwardAdjunction i).unit.app L) (𝟙 _) ≫
      pushforwardTensorMap i _ _ = _
  rw [← Category.assoc, tensorSheafMap_comp]
  simp only [Category.id_comp, Category.comp_id]

/-- A native whole-boundary equation gives the literal pulled-back section equation. -/
theorem pullback_section_of_boundary_equation {Z C : Scheme.{u}}
    (i : Z ⟶ C) [IsClosedImmersion i] (L M : C.Modules)
    (s : SheafOfModules.unit C.ringCatSheaf ⟶ (moduleTensorLeftFunctor C L).obj M)
    (t : SheafOfModules.unit Z.ringCatSheaf ⟶
      (moduleTensorLeftFunctor Z ((Modules.pullback i).obj L)).obj
        ((Modules.pullback i).obj M))
    (h : s ≫ boundaryRestriction i L M =
      SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom ≫
        (Modules.pushforward i).map t) :
    (pullbackUnitIso i).inv ≫ (Modules.pullback i).map s ≫ pullbackTensorMap i L M = t := by
  have ht : (Modules.pullback i).map s ≫ pullbackTensorMap i L M =
      (pullbackUnitIso i).hom ≫ t := by
    apply ((pullbackPushforwardAdjunction i).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      pullbackUnitIso_homEquiv]
    rw [boundaryRestriction_eq_adjoint] at h
    exact h
  rw [ht]
  simp

/-- The actual equality of global sections is enough; no sheaf-map lift is assumed. -/
theorem pullback_section_of_boundary_value {Z C : Scheme.{u}}
    (i : Z ⟶ C) [IsClosedImmersion i] (L M : C.Modules)
    (s : Γ((moduleTensorLeftFunctor C L).obj M, ⊤))
    (σ : Γ((moduleTensorLeftFunctor Z ((Modules.pullback i).obj L)).obj
      ((Modules.pullback i).obj M), ⊤))
    (h : (boundaryRestriction i L M).app ⊤ s =
      ((moduleTensorLeftFunctor Z ((Modules.pullback i).obj L)).obj
        ((Modules.pullback i).obj M)).presheaf.map
          (eqToHom (show i ⁻¹ᵁ ⊤ = ⊤ by simp)).op σ) :
    (pullbackUnitIso i).inv ≫ (Modules.pullback i).map
      ((unitHomGlobalSectionsEquiv C _).symm s) ≫ pullbackTensorMap i L M =
        (unitHomGlobalSectionsEquiv Z _).symm σ := by
  apply pullback_section_of_boundary_equation
  apply (unitHomGlobalSectionsEquiv C _).injective
  rw [unitHomGlobalSectionsEquiv_naturality, Equiv.apply_symm_apply]
  change (boundaryRestriction i L M).app ⊤ s =
    Modules.Hom.app ((unitHomGlobalSectionsEquiv Z _).symm σ) (i ⁻¹ᵁ ⊤) (i.app ⊤ 1)
  rw [map_one, unitHomGlobalSectionsEquiv_symm_app, one_smul]
  exact h
end AlgebraicGeometry.Scheme.CoherentGraph
