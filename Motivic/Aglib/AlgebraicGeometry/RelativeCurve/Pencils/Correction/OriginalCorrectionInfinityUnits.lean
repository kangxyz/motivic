/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.GraphInfinityEquality
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.InfinityBoundaryIdeal
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.FunctionalQuotientAffineChart
/-! # The original infinity units used by the correction action

The all-parameter graph ideal is a unit on infinity, not on the marked incidence.
The smaller action boundary and the normalization boundary remain distinct.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalCorrectionInfinityUnits`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Norm.OriginalPairNormBoundaryUnits`, `Pencils.NativeCorrectionTransferAction`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- A section unit on the original full boundary remains a unit on its entire
infinity summand, without any first-parameter restriction. -/
theorem pullbackSectionMap_coprod_left_isIso
    {C B D : Scheme.{u}} (b : B ⟶ C) (d : D ⟶ C) {M : C.Modules}
    (s : SheafOfModules.unit C.ringCatSheaf ⟶ M)
    [IsIso (pullbackSectionMap (coprod.desc b d) s)] :
    IsIso (pullbackSectionMap b s) := by
  have hi : IsIso (pullbackSectionMap
      (coprod.inl ≫ coprod.desc b d) s) := by
    rw [← pullbackSectionMap_comp]
    have : IsIso (pullbackSectionMap coprod.inl
        (pullbackSectionMap (coprod.desc b d) s)) := by
      change IsIso ((pullbackUnitIso coprod.inl).inv ≫
        (Modules.pullback coprod.inl).map (pullbackSectionMap (coprod.desc b d) s))
      infer_instance
    infer_instance
  exact (congrArg (fun f => IsIso (pullbackSectionMap f s))
    (coprod.inl_desc b d)).mp hi

/-- Removing the canonical unit-object isomorphism preserves invertibility. -/
theorem pullback_map_isIso_of_pullbackUnitMap
    {C B : Scheme.{u}} (b : B ⟶ C) {M : C.Modules}
    (φ : M ⟶ SheafOfModules.unit C.ringCatSheaf)
    [IsIso (pullbackUnitMap b φ)] : IsIso ((Modules.pullback b).map φ) := by
  have hi : IsIso ((Modules.pullback b).map φ ≫ (pullbackUnitIso b).hom) :=
    inferInstanceAs (IsIso (pullbackUnitMap b φ))
  exact IsIso.of_isIso_comp_right _ (pullbackUnitIso b).hom

/-- The exact original commutative square transports a functional boundary unit
through first-parameter pullback. No source integrality or regularity is needed. -/
theorem pullback_map_unit_isIso_of_comm
    {C T B E : Scheme.{u}} (τ : T ⟶ C) (b : B ⟶ C)
    (i : E ⟶ T) (l : E ⟶ B) (h : i ≫ τ = l ≫ b)
    {M : C.Modules} (φ : M ⟶ SheafOfModules.unit C.ringCatSheaf)
    [IsIso ((Modules.pullback b).map φ)] :
    IsIso ((Modules.pullback i).map (pullbackUnitMap τ φ)) := by
  let : IsIso (pullbackUnitMap b φ) := by
    change IsIso ((Modules.pullback b).map φ ≫ (pullbackUnitIso b).hom)
    infer_instance
  have hc := pullbackUnitMap_comp_isIso_of_first b l φ
  rw [← h] at hc
  let := hc
  let := pullbackUnitMap_nested_isIso_of_comp τ i φ
  exact pullback_map_isIso_of_pullbackUnitMap i (pullbackUnitMap τ φ)

end AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Hom

/-- The actual graph ideal inclusion is invertible on the original infinity
scheme, without a false assertion on the marked incidence. -/
theorem correctionInfinity_pullbackIdealInclusion_isIso
    {S C Y D : Scheme.{u}} (π : C ⟶ S) [IsSeparated π]
    (j : Y ⟶ C) [IsOpenImmersion j]
    (d : D ⟶ C)
    (hd : Disjoint (Set.range j) (Set.range d)) :
    IsIso ((Modules.pullback (infinityProductMap π j d)).map
      (idealInclusion (compactificationGraph π j))) := by
  have h : IsIso (pullbackUnitMap (infinityProductMap π j d)
      (idealInclusion (compactificationGraph π j))) := by
    change IsIso ((Modules.pullback (infinityProductMap π j d)).map
      (idealInclusion (compactificationGraph π j)) ≫
        SheafOfModules.pullbackObjUnitToUnit (infinityProductMap π j d).toRingCatSheafHom)
    exact infinity_pullbackIdealInclusion_isIso π j d hd
  let := h
  exact pullback_map_isIso_of_pullbackUnitMap _ _

end AlgebraicGeometry.Scheme.Hom
