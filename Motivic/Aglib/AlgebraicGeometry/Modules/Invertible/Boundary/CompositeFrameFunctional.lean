/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.PrescribedPairPullback
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.Neighborhood.General

/-! # Functional coordinates in the existing composite boundary frame

Intended upstream module:
`Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.CompositeFrameFunctional`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.ParameterGraphChartFrame`,
`Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RetainedTargetChartFrame`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- The ideal-functional direction retains the same original frame and scalar. -/
theorem compositeBoundaryFrame_functional_coordinate {X Y W : Scheme.{u}}
    (f : W ⟶ Y) (g : Y ⟶ X) (M : X.Modules)
    (E : (Modules.pullback g).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (compositeBoundaryFrame f g M E).inv ≫ pullbackUnitMap (f ≫ g) φ =
      Scheme.Hom.unitEndomorphismPullback f (E.inv ≫ pullbackUnitMap g φ) := by
  simp only [compositeBoundaryFrame, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Category.assoc]
  rw [pullbackUnitMap_comp]
  simp only [Scheme.Hom.unitEndomorphismPullback, pullbackUnitMap,
    Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Scheme.Modules.Invertible
