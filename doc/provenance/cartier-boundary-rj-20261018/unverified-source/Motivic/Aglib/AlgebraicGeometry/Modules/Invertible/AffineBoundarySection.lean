/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteGenerators
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.BoundarySectionLifting
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.SectionDualFunctional

/-!
# Prescribed line-bundle sections along a closed affine boundary

A section on the entire closed boundary lifts on the unchanged affine ambient
scheme. In particular a specified boundary frame has an actual section lifting
its inverse. No pointwise shrinking, semilocal hypothesis, projective twist or
extra section-existence input is used. This prepares a boundary-unit section;
it does not assert a global Cartier representative on a proper compactification.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An epimorphism between quasicoherent sheaves induces an epimorphism on
actual affine global sections, through the original tilde counit. -/
theorem epi_globalSections_of_epi_quasicoherent (R : CommRingCat.{u})
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] : Epi (moduleSpecΓFunctor.map f) := by
  have : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M
  have : IsIso N.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent N
  have h := fromTildeΓNatTrans.naturality f
  change (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
    M.fromTildeΓ ≫ f at h
  have he : (tilde.functor R).map (moduleSpecΓFunctor.map f) =
      M.fromTildeΓ ≫ f ≫ inv N.fromTildeΓ := by
    rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hf : Epi ((tilde.functor R).map (moduleSpecΓFunctor.map f)) := by
    rw [he]
    infer_instance
  exact (tilde.functor R).epi_of_epi_map hf

/-- The actual structure-module map lifts across a quasicoherent affine epi. -/
theorem exists_unitHom_lift_of_epi_quasicoherent (R : CommRingCat.{u})
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] (s : SheafOfModules.unit (Spec R).ringCatSheaf ⟶ N) :
    ∃ t : SheafOfModules.unit (Spec R).ringCatSheaf ⟶ M, t ≫ f = s := by
  have := epi_globalSections_of_epi_quasicoherent R f
  have hf := (ModuleCat.epi_iff_surjective (moduleSpecΓFunctor.map f)).mp inferInstance
  obtain ⟨t, ht⟩ := hf (unitHomGlobalSectionsEquiv (Spec R) N s)
  refine ⟨(unitHomGlobalSectionsEquiv (Spec R) M).symm t, ?_⟩
  apply (unitHomGlobalSectionsEquiv (Spec R) N).injective
  rw [unitHomGlobalSectionsEquiv_naturality, Equiv.apply_symm_apply]
  exact ht

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Invertible

open Scheme.Modules.QuasiCoherent

/-- Every section of the original pulled-back line bundle on a closed boundary
has a section lift on the entire affine scheme, with its literal pullback value. -/
theorem exists_section_with_prescribed_closed_boundary (R : CommRingCat.{u})
    {Z : Scheme.{u}} (z : Z ⟶ Spec R) [IsClosedImmersion z]
    (L : LineBundle (Spec R))
    (s : SheafOfModules.unit Z.ringCatSheaf ⟶ (Modules.pullback z).obj L.val) :
    ∃ t : SheafOfModules.unit (Spec R).ringCatSheaf ⟶ L.val,
      pullbackSectionMap z t = s := by
  let adj := Modules.pullbackPushforwardAdjunction z
  let N := (Modules.pushforward z).obj ((Modules.pullback z).obj L.val)
  have : IsFiniteLocallyFree (Spec R) L.val :=
    finiteLocallyFree_of_isLocallyRankOne L.val L.property
  have : L.val.IsQuasicoherent := inferInstance
  have : IsFiniteLocallyFree Z (pullbackLineBundle z L).val :=
    finiteLocallyFree_of_isLocallyRankOne _ (pullbackLineBundle z L).property
  have hN : affineLocallyFiniteType (Spec R) N :=
    FiniteMorphism.affineLocallyFiniteType_pushforward z
      (coherent_of_finiteLocallyFree (pullbackLineBundle z L).val)
  have : N.IsQuasicoherent := ((affineLocallyFiniteType_spec_iff R N).mp hN).1
  have : Epi (adj.unit.app L.val) :=
    pullbackPushforwardUnit_epi_of_closedImmersion z L.val
  let b := (adj.homEquiv (SheafOfModules.unit (Spec R).ringCatSheaf)
    ((Modules.pullback z).obj L.val)) ((pullbackUnitIso z).hom ≫ s)
  obtain ⟨t, ht⟩ := exists_unitHom_lift_of_epi_quasicoherent R (adj.unit.app L.val) b
  refine ⟨t, ?_⟩
  have he : (Modules.pullback z).map t = (pullbackUnitIso z).hom ≫ s := by
    apply (adj.homEquiv _ _).injective
    have hn := adj.homEquiv_naturality_left t (𝟙 ((Modules.pullback z).obj L.val))
    calc
      _ = t ≫ adj.unit.app L.val := by
        simpa only [Category.comp_id, Adjunction.homEquiv_id] using hn
      _ = b := ht
      _ = _ := rfl
  rw [pullbackSectionMap, he, Iso.inv_hom_id_assoc]

/-- The specified frame is extended, rather than replacing it by an unrelated
trivialization. The conclusion is on the unchanged original affine scheme. -/
theorem exists_section_extending_closed_frame (R : CommRingCat.{u})
    {Z : Scheme.{u}} (z : Z ⟶ Spec R) [IsClosedImmersion z]
    (L : LineBundle (Spec R))
    (e : (Modules.pullback z).obj L.val ≅ SheafOfModules.unit Z.ringCatSheaf) :
    ∃ t : SheafOfModules.unit (Spec R).ringCatSheaf ⟶ L.val,
      pullbackSectionMap z t = e.inv :=
  exists_section_with_prescribed_closed_boundary R z L e.inv

/-- The prescribed frame produces a section whose whole zero scheme misses
 the entire closed boundary, not merely its selected residue-field points. -/
theorem exists_section_extending_closed_frame_avoiding_boundary (R : CommRingCat.{u})
    {Z : Scheme.{u}} (z : Z ⟶ Spec R) [IsClosedImmersion z]
    (L : LineBundle (Spec R))
    (e : (Modules.pullback z).obj L.val ≅ SheafOfModules.unit Z.ringCatSheaf) :
    ∃ t : SheafOfModules.unit (Spec R).ringCatSheaf ⟶ L.val,
      pullbackSectionMap z t = e.inv ∧
        IsEmpty (pullback z (Hom.zeroInclusion (sectionDualFunctional (Spec R) L t))) := by
  obtain ⟨t, ht⟩ := exists_section_extending_closed_frame R z L e
  have : IsIso (pullbackSectionMap z t) := by rw [ht]; infer_instance
  exact ⟨t, ht, sectionDualFunctional_boundary_isEmpty z L t⟩

end AlgebraicGeometry.Scheme.Modules.Invertible
