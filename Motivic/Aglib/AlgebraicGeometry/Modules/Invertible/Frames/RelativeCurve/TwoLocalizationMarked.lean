/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.BaseChange.TwoLocalizationMarked
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Graph.Retained
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateUnitOnOpen
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryCanonicalCoordinate

/-!
# Preserve the chosen marked frame on the actual twice-localized curve

The supplied original marked ideal frame is transported through the two literal
restricted graph ideals and the actual flat product map. Its exact scalar is
preserved. Dualization is performed on the final original graph ideal line, so
the resulting frame splits the positive divisor line, not the ideal line.
The canonical infinity frame then glues with this same marked frame on the
whole pulled-back boundary, with both coproduct component equations retained.

Intended upstream module:
`Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.TwoLocalizationMarked`.
Current consumer: the same-witness two-localization relative-affine-line
normalization assembly. Finiteness supplies separated compactification maps;
relative smoothness is required only on the original retained curve. The
original frame remains an explicit input here and is supplied by the native
affine-line coordinate construction in the application. There is no global
Picard premise, recomputed frame equality, or normal/reduced fiber assumption.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme Scheme.Hom Scheme.Modules Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.RelativeProjectiveLine.TwoLocalizations

variable (R : Type u) [CommRing R] (r : R) (s : Localization.Away r)
  {C Y Z : Scheme.{u}} (F : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
  (j : Y ⟶ C) (z : Z ⟶ Y)

local notation "q₀" => F ≫ ProjectiveSpace.toSpec R (ULift (Fin 2))
local notation "q₂" => projection R r s F
local notation "j₂" => retainedInclusion R r s F j
local notation "yρ" => retainedSourceMap R r s F j
local notation "zρ" => markedSourceMap R r s F j z
local notation "s₂" => markedLift R r s F j z
local notation "M₀" => pullback (j ≫ q₀) (z ≫ j ≫ q₀)
local notation "M₂" => pullback (j₂ ≫ q₂) (s₂ ≫ j₂ ≫ q₂)

variable [IsFinite F] [IsOpenImmersion j]

/-- Transport the chosen initial marked ideal frame through literal restricted graph ideals. -/
def markedIdealFrame
    (e : SheafOfModules.unit (M₀).ringCatSheaf ≅
      (Modules.pullback (graphBoundaryRestriction q₀ j z)).obj
        (idealModule (compactificationGraph q₀ j))) :
    SheafOfModules.unit (M₂).ringCatSheaf ≅
      (Modules.pullback (graphBoundaryRestriction q₂ j₂ s₂)).obj
        (idealModule (compactificationGraph q₂ j₂)) := by
  have : IsClosedImmersion (compactificationGraph q₀ j) := by
    dsimp [compactificationGraph]
    infer_instance
  have : IsClosedImmersion (compactificationGraph q₂ j₂) := by
    dsimp [compactificationGraph]
    infer_instance
  let w₀ := idealPullbackMap (compactificationGraph q₀ j)
    (restrictedBoundaryGraph q₀ j z) (graphBoundaryRestriction q₀ j z) z
    (compactificationGraph_boundary_isPullback q₀ j z).w
  have : IsIso w₀ := compactificationGraph_boundaryIdealMap_isIso q₀ j z
  let w₂ := idealPullbackMap (compactificationGraph q₂ j₂)
    (restrictedBoundaryGraph q₂ j₂ s₂) (graphBoundaryRestriction q₂ j₂ s₂) s₂
    (compactificationGraph_boundary_isPullback q₂ j₂ s₂).w
  have : IsIso w₂ := compactificationGraph_boundaryIdealMap_isIso q₂ j₂ s₂
  have : IsClosedImmersion (restrictedBoundaryGraph q₀ j z) :=
    MorphismProperty.of_isPullback (compactificationGraph_boundary_isPullback q₀ j z)
      inferInstance
  let := Scheme.Modules.unit_isLocallyFree M₀
  have : (idealModule (restrictedBoundaryGraph q₀ j z)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent _).prop_of_iso (e ≪≫ asIso w₀) inferInstance
  let H := markedGraphSquare R r s F j z
  have : IsClosedImmersion (restrictedBoundaryGraph q₂ j₂ s₂) :=
    MorphismProperty.of_isPullback H inferInstance
  let v := idealPullbackMap (restrictedBoundaryGraph q₀ j z)
    (restrictedBoundaryGraph q₂ j₂ s₂) (markedProductMap R r s F j z) zρ H.w
  have : IsIso v := idealPullbackMap_isIso_of_flat_ambient _ _ _ _ _ H
  exact (pullbackUnitIso (markedProductMap R r s F j z)).symm ≪≫
    (Modules.pullback (markedProductMap R r s F j z)).mapIso (e ≪≫ asIso w₀) ≪≫
      asIso v ≪≫ (asIso w₂).symm

/-- The exact pulled scalar is preserved on the whole marked scheme. -/
theorem markedIdealFrame_coordinate
    (e : SheafOfModules.unit (M₀).ringCatSheaf ≅
      (Modules.pullback (graphBoundaryRestriction q₀ j z)).obj
        (idealModule (compactificationGraph q₀ j))) :
    (markedIdealFrame R r s F j z e).hom ≫
      Modules.Hom.pullbackToUnit (idealInclusion (compactificationGraph q₂ j₂))
        (graphBoundaryRestriction q₂ j₂ s₂) =
    unitEndomorphismPullback (markedProductMap R r s F j z)
      (e.hom ≫ Modules.Hom.pullbackToUnit (idealInclusion (compactificationGraph q₀ j))
        (graphBoundaryRestriction q₀ j z)) := by
  dsimp only [markedIdealFrame, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_hom, asIso_inv]
  simp only [Category.assoc]
  unfold Modules.Hom.pullbackToUnit
  erw [← idealPullbackMap_inclusion (compactificationGraph q₂ j₂)
    (restrictedBoundaryGraph q₂ j₂ s₂) (graphBoundaryRestriction q₂ j₂ s₂) s₂
    (compactificationGraph_boundary_isPullback q₂ j₂ s₂).w]
  rw [IsIso.inv_hom_id_assoc, idealPullbackMap_inclusion]
  simp only [unitEndomorphismPullback, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc, idealPullbackMap_inclusion, Functor.map_comp]
  rfl

variable [hsm : SmoothOfRelativeDimension 1
  (j ≫ (F ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))]

include hsm in
local instance : SmoothOfRelativeDimension 1 (j₂ ≫ q₂) :=
  @retainedProjection_smooth R _ r s C Y F j hsm

/-- The positive diagonal/divisor line, not the ideal line, is split on the exact marked product. -/
def markedDivisorFrame
    (e : SheafOfModules.unit (M₀).ringCatSheaf ≅
      (Modules.pullback (graphBoundaryRestriction q₀ j z)).obj
        (idealModule (compactificationGraph q₀ j))) :
    (Modules.pullback (graphBoundaryRestriction q₂ j₂ s₂)).obj
      (dualLineBundle _ (relativeCompactificationGraphLine q₂ j₂)).val ≅
        SheafOfModules.unit (M₂).ringCatSheaf :=
  dualBoundaryTrivialization _ (relativeCompactificationGraphLine q₂ j₂)
    (markedIdealFrame R r s F j z e)


/-- The canonical positive-divisor section has precisely the pulled original scalar. -/
theorem markedDivisorFrame_coordinate
    (e : SheafOfModules.unit (M₀).ringCatSheaf ≅
      (Modules.pullback (graphBoundaryRestriction q₀ j z)).obj
        (idealModule (compactificationGraph q₀ j))) :
    pullbackCanonicalDualHom (graphBoundaryRestriction q₂ j₂ s₂)
      (relativeCompactificationGraphLine q₂ j₂) (idealInclusion (compactificationGraph q₂ j₂)) ≫
        (markedDivisorFrame R r s F j z e).hom =
      unitEndomorphismPullback (markedProductMap R r s F j z)
        (e.hom ≫ Modules.Hom.pullbackToUnit (idealInclusion (compactificationGraph q₀ j))
          (graphBoundaryRestriction q₀ j z)) := by
  rw [markedDivisorFrame, dualBoundaryTrivialization_canonical]
  exact markedIdealFrame_coordinate R r s F j z e

/-- Glue the preserved marked frame to the canonical frame on the whole pulled boundary. -/
theorem exists_fullBoundaryDivisorFrame
    (e : SheafOfModules.unit (M₀).ringCatSheaf ≅
      (Modules.pullback (graphBoundaryRestriction q₀ j z)).obj
        (idealModule (compactificationGraph q₀ j)))
    {D : Scheme.{u}} (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d)) :
    let d₂ := pullback.snd d (sourceMap R r s F)
    let A₂ := pullback (pullback.snd (j₂ ≫ q₂) q₂) d₂
    let a := infinityProductMap q₂ j₂ d₂
    let b := graphBoundaryRestriction q₂ j₂ s₂
    let L := (dualLineBundle _ (relativeCompactificationGraphLine q₂ j₂)).val
    ∃ E : (Modules.pullback (coprod.desc a b)).obj L ≅
        SheafOfModules.unit (A₂ ⨿ M₂).ringCatSheaf,
      (Modules.restrictFunctor (coprod.inl : A₂ ⟶ A₂ ⨿ M₂)).map E.hom ≫
          (restrictUnitIso _).hom = (coprodPullbackRestrictLeft a b).hom.app L ≫
            (infinityBoundaryDivisorIso q₂ j₂ d₂
              (retainedBoundary_disjoint R r s F j d hd)
              (relativeCompactificationGraphLine q₂ j₂).property).hom ∧
      (Modules.restrictFunctor (coprod.inr : M₂ ⟶ A₂ ⨿ M₂)).map E.hom ≫
          (restrictUnitIso _).hom = (coprodPullbackRestrictRight a b).hom.app L ≫
            (markedDivisorFrame R r s F j z e).hom := by
  dsimp only
  exact exists_coprod_pullback_unitIso _ _ _
    (infinityBoundaryDivisorIso q₂ j₂ (pullback.snd d (sourceMap R r s F))
      (retainedBoundary_disjoint R r s F j d hd)
      (relativeCompactificationGraphLine q₂ j₂).property)
    (markedDivisorFrame R r s F j z e)

end AlgebraicGeometry.RelativeProjectiveLine.TwoLocalizations
