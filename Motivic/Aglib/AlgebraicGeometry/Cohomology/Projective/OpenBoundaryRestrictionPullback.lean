/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.BoundaryRestrictionPullback
public import Motivic.Aglib.AlgebraicGeometry.Modules.StructureSheaf.OpenSectionHom
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Restriction
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.BoundaryUnitSection
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Isomorphism
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.SectionDualFunctional

/-! # Literal pullback of sections prescribed on an open boundary -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.Modules.Pullback.OpenRestriction
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- The prescribed unit boundary section is the inverse of its actual
trivialization after conversion to a unit-domain sheaf morphism. -/
theorem openSectionHom_unit_boundary {Z : Scheme.{u}} (W : Z.Opens) (N : Z.Modules)
    (e : N.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) :
    openSectionHom Z W N ((openUnitSectionsIso W N e).inv (1 : Γ(W.toScheme, ⊤))) =
      e.inv := by
  unfold openSectionHom
  rw [openSection_eq_restrictedSectionsIso, openUnitSectionsIso_inv_one_restrict]
  apply (unitHomGlobalSectionsEquiv W.toScheme _).injective
  rw [Equiv.apply_symm_apply]
  rfl

/-- Propositionally equal boundary opens retain the same actual unit section. -/
theorem isIso_openSectionHom_unit_boundary_of_eq {X : Scheme.{u}}
    (U V : X.Opens) (h : U = V) (Q : X.Modules)
    (e : Q.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) :
    IsIso (openSectionHom X U Q
      ((Q.presheaf.mapIso (eqToIso h).op).hom
        ((openUnitSectionsIso V Q e).inv (1 : Γ(V.toScheme, ⊤))))) := by
  subst V
  simp only [eqToIso_refl, Iso.op_refl, Functor.mapIso_refl, Iso.refl_hom,
    ConcreteCategory.id_apply]
  rw [openSectionHom_unit_boundary]
  infer_instance

/-- A boundary equation on an arbitrary open gives the actual pulled-back
unit-domain section under the native open-restriction and tensor comparisons. -/
theorem pullback_openSection_of_boundary_value {Z C : Scheme.{u}}
    (z : Z ⟶ C) [IsClosedImmersion z] (L M : C.Modules) (U : C.Opens)
    (s : Γ((moduleTensorLeftFunctor C L).obj M, U))
    (σ : Γ((moduleTensorLeftFunctor Z ((Modules.pullback z).obj L)).obj
      ((Modules.pullback z).obj M), z ⁻¹ᵁ U))
    (h : (boundaryRestriction z L M).app U s = σ) :
    (pullbackUnitIso (z ∣_ U)).inv ≫ (Modules.pullback (z ∣_ U)).map
        (openSectionHom C U ((moduleTensorLeftFunctor C L).obj M) s) ≫
      (localPullbackIso z U).inv.app ((moduleTensorLeftFunctor C L).obj M) ≫
      (Modules.restrictFunctor (z ⁻¹ᵁ U).ι).map (pullbackTensorMap z L M) =
      openSectionHom Z (z ⁻¹ᵁ U)
        ((moduleTensorLeftFunctor Z ((Modules.pullback z).obj L)).obj
          ((Modules.pullback z).obj M)) σ := by
  let T := (moduleTensorLeftFunctor C L).obj M
  let N := (moduleTensorLeftFunctor Z ((Modules.pullback z).obj L)).obj
    ((Modules.pullback z).obj M)
  let β : (Modules.pullback (z ∣_ U)).obj (T.restrict U.ι) ⟶
      N.restrict (z ⁻¹ᵁ U).ι := (localPullbackIso z U).inv.app T ≫
    (Modules.restrictFunctor (z ⁻¹ᵁ U).ι).map (pullbackTensorMap z L M)
  have hh : ((pullbackPushforwardAdjunction z).homEquiv _ _).symm
      (boundaryRestriction z L M) = pullbackTensorMap z L M := by
    rw [boundaryRestriction_eq_adjoint]
    exact Equiv.symm_apply_apply _ _
  have hn := restrictedAdjoint_eq z U (boundaryRestriction z L M)
  rw [hh] at hn
  have hβ : β = ((pullbackPushforwardAdjunction (z ∣_ U)).homEquiv _ _).symm
      ((Modules.restrictFunctor U.ι).map (boundaryRestriction z L M) ≫
        restrictedPushforwardMap z U N) := by
    dsimp only [β]
    rw [hn]
    dsimp only [T, N]
    erw [Iso.inv_hom_id_app_assoc]
  have hadj : (pullbackPushforwardAdjunction (z ∣_ U)).homEquiv _ _ β =
      (Modules.restrictFunctor U.ι).map (boundaryRestriction z L M) ≫
        restrictedPushforwardMap z U N := by
    rw [hβ]
    exact Equiv.apply_symm_apply _ _
  have ht : (Modules.pullback (z ∣_ U)).map (openSectionHom C U T s) ≫ β =
      (pullbackUnitIso (z ∣_ U)).hom ≫ openSectionHom Z (z ⁻¹ᵁ U) N σ := by
    apply ((pullbackPushforwardAdjunction (z ∣_ U)).homEquiv _ _).injective
    erw [Adjunction.homEquiv_naturality_left, hadj]
    erw [Adjunction.homEquiv_naturality_right, pullbackUnitIso_homEquiv]
    rw [← Category.assoc, openSectionHom_naturality, h, openSectionHom_pushforward]
  change (pullbackUnitIso (z ∣_ U)).inv ≫
    (Modules.pullback (z ∣_ U)).map (openSectionHom C U T s) ≫ β = _
  rw [ht]
  simp only [Iso.inv_hom_id_assoc]
  rfl

/-- The actual prescribed unit boundary produces the literal inverse
trivialization on the entire original restricted boundary. -/
theorem pullback_openSection_of_unit_boundary {Z C : Scheme.{u}}
    (z : Z ⟶ C) [IsClosedImmersion z] (L M : C.Modules) (U : C.Opens)
    (s : Γ((moduleTensorLeftFunctor C L).obj M, U))
    (e : (((moduleTensorLeftFunctor Z ((Modules.pullback z).obj L)).obj
      ((Modules.pullback z).obj M)).restrict (z ⁻¹ᵁ U).ι) ≅
        SheafOfModules.unit (z ⁻¹ᵁ U).toScheme.ringCatSheaf)
    (h : (boundaryRestriction z L M).app U s =
      (openUnitSectionsIso (z ⁻¹ᵁ U) _ e).inv (1 : Γ((z ⁻¹ᵁ U).toScheme, ⊤))) :
    (pullbackUnitIso (z ∣_ U)).inv ≫ (Modules.pullback (z ∣_ U)).map
        (openSectionHom C U ((moduleTensorLeftFunctor C L).obj M) s) ≫
      (localPullbackIso z U).inv.app ((moduleTensorLeftFunctor C L).obj M) ≫
      (Modules.restrictFunctor (z ⁻¹ᵁ U).ι).map (pullbackTensorMap z L M) = e.inv := by
  rw [pullback_openSection_of_boundary_value z L M U s _ h, openSectionHom_unit_boundary]

/-- A unit boundary value makes the actual normalized pullback section invertible.
The native tensor comparison is invertible even without a line-bundle hypothesis. -/
theorem isIso_pullback_openSection_of_boundary_value {Z C : Scheme.{u}}
    (z : Z ⟶ C) [IsClosedImmersion z] (L M : C.Modules) (U : C.Opens)
    (s : Γ((moduleTensorLeftFunctor C L).obj M, U))
    (σ : Γ((moduleTensorLeftFunctor Z ((Modules.pullback z).obj L)).obj
      ((Modules.pullback z).obj M), z ⁻¹ᵁ U))
    (h : (boundaryRestriction z L M).app U s = σ)
    [IsIso (openSectionHom Z (z ⁻¹ᵁ U)
      ((moduleTensorLeftFunctor Z ((Modules.pullback z).obj L)).obj
        ((Modules.pullback z).obj M)) σ)] :
    IsIso (pullbackSectionMap (z ∣_ U)
      (openSectionHom C U ((moduleTensorLeftFunctor C L).obj M) s)) := by
  have : IsIso (pullbackTensorMap z L M) :=
    Modules.Pullback.Tensor.pullbackTensorMap_isIso z L M
  let c := (localPullbackIso z U).inv.app ((moduleTensorLeftFunctor C L).obj M) ≫
    (Modules.restrictFunctor (z ⁻¹ᵁ U).ι).map (pullbackTensorMap z L M)
  have : IsIso c := inferInstance
  have hcomp : IsIso (pullbackSectionMap (z ∣_ U)
      (openSectionHom C U ((moduleTensorLeftFunctor C L).obj M) s) ≫ c) := by
    change IsIso ((pullbackUnitIso (z ∣_ U)).inv ≫ (Modules.pullback (z ∣_ U)).map
      (openSectionHom C U ((moduleTensorLeftFunctor C L).obj M) s) ≫ c)
    dsimp only [c]
    rw [pullback_openSection_of_boundary_value z L M U s σ h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ c

end AlgebraicGeometry.Scheme.CoherentGraph
