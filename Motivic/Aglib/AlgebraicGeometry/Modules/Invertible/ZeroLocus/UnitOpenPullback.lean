/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.UnitOpen
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.Neighborhood.General

/-! # Actual functional units on maps into the original unit domain

Intended upstream module: `Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.UnitOpenPullback`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RetainedUnitDomain`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- A map into the original zero-support complement makes this exact pulled
functional invertible. The lift uses the existing unit domain, not a new frame. -/
theorem isIso_pullbackUnitMap_of_range_subset_unitOpen
    {X W : Scheme.{u}} (L : LineBundle X)
    (φ : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) (w : W ⟶ X)
    (hw : Set.range w ⊆ (zeroSupportUnitOpen L φ : Set X)) :
    IsIso (pullbackUnitMap w φ) := by
  let U := zeroSupportUnitOpen L φ
  have hU : Set.range w ⊆ Set.range U.ι := by simpa only [Scheme.Opens.range_ι] using hw
  let t := IsOpenImmersion.lift U.ι w hU
  have ht : t ≫ U.ι = w := IsOpenImmersion.lift_fac _ _ _
  have : IsIso ((Modules.pullback U.ι).map φ) := isIso_pullback_zeroSupportUnitOpen L φ
  have : IsIso (pullbackUnitMap U.ι φ) := by
    change IsIso ((Modules.pullback U.ι).map φ ≫ (pullbackUnitIso U.ι).hom)
    infer_instance
  have : IsIso (pullbackUnitMap t (pullbackUnitMap U.ι φ)) := by
    change IsIso ((Modules.pullback t).map (pullbackUnitMap U.ι φ) ≫ (pullbackUnitIso t).hom)
    infer_instance
  have : IsIso (((Modules.pullbackComp t U.ι).app L.val).hom ≫
      pullbackUnitMap (t ≫ U.ι) φ) := by
    rw [pullbackUnitMap_comp]
    infer_instance
  have : IsIso (pullbackUnitMap (t ≫ U.ι) φ) :=
    IsIso.of_isIso_comp_left ((Modules.pullbackComp t U.ι).app L.val).hom _
  have : IsIso (((Modules.pullbackCongr ht).app L.val).hom ≫
      pullbackUnitMap w φ) := by
    rw [pullbackUnitMap_congr]
    infer_instance
  exact IsIso.of_isIso_comp_left ((Modules.pullbackCongr ht).app L.val).hom _

end AlgebraicGeometry.Scheme.Modules.Invertible
