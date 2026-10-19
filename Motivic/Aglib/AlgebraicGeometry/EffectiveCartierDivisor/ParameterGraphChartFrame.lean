/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.ParameterGraphPullback
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.CompositeFrameFunctional

/-! # The same target graph frame on the actual parameter-pullback chart

The target frame is pulled along the second projection of its original chart.
The native graph ideal comparison identifies its domain, and its functional
coordinate remains exactly the pullback of the original target coordinate.


Intended upstream module:
`Aglib.AlgebraicGeometry.EffectiveCartierDivisor.ParameterGraphChartFrame`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RetainedParameterGraph`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S C X Y W : Scheme.{u}} (q : C ⟶ S) (j : X ⟶ C) (p : Y ⟶ X) [Flat p]
  [IsClosedImmersion (compactificationGraph q j)]
  [IsClosedImmersion (compactificationGraph q (p ≫ j))]
  (hI : IsLocallyRankOne _ (idealModule (compactificationGraph q j)))
  (v : W ⟶ pullback (j ≫ q) q)
  (e : (Modules.pullback v).obj (idealModule (compactificationGraph q j)) ≅
    SheafOfModules.unit W.ringCatSheaf)

/-- The SAME original target frame, pulled to the literal inverse chart. -/
def parameterGraphChartFrame :
    (Modules.pullback (pullback.fst (parameterProductMap q j p) v)).obj
      (idealModule (compactificationGraph q (p ≫ j))) ≅
        SheafOfModules.unit (pullback (parameterProductMap q j p) v).ringCatSheaf :=
  (Modules.pullback (pullback.fst (parameterProductMap q j p) v)).mapIso
      (parameterGraphIdealIso q j p hI).symm ≪≫
    (Modules.pullbackComp (pullback.fst (parameterProductMap q j p) v)
      (parameterProductMap q j p)).app (idealModule (compactificationGraph q j)) ≪≫
    (Modules.pullbackCongr (pullback.condition (f := parameterProductMap q j p) (g := v))).app
      (idealModule (compactificationGraph q j)) ≪≫
    compositeBoundaryFrame (pullback.snd (parameterProductMap q j p) v) v
      (idealModule (compactificationGraph q j)) e

/-- The actual pulled target coordinate is exactly the same functional coordinate,
not merely an associated graph generator. -/
theorem parameterGraphChartFrame_coordinate :
    (parameterGraphChartFrame q j p hI v e).inv ≫
      pullbackUnitMap (pullback.fst (parameterProductMap q j p) v)
        (idealInclusion (compactificationGraph q (p ≫ j))) =
    unitEndomorphismPullback (pullback.snd (parameterProductMap q j p) v)
      (e.inv ≫ pullbackUnitMap v (idealInclusion (compactificationGraph q j))) := by
  have hi :
      (Modules.pullback (pullback.fst (parameterProductMap q j p) v)).map
          (parameterGraphIdealIso q j p hI).hom ≫
        pullbackUnitMap (pullback.fst (parameterProductMap q j p) v)
          (idealInclusion (compactificationGraph q (p ≫ j))) =
      pullbackUnitMap (pullback.fst (parameterProductMap q j p) v)
        (pullbackUnitMap (parameterProductMap q j p)
          (idealInclusion (compactificationGraph q j))) := by
    dsimp only [pullbackUnitMap]
    rw [← Functor.map_comp_assoc, parameterGraphIdealIso_inclusion]
    rfl
  simp only [parameterGraphChartFrame, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Category.assoc]
  rw [hi, ← pullbackUnitMap_comp, Iso.inv_hom_id_assoc,
    ← pullbackUnitMap_congr, Iso.inv_hom_id_assoc,
    compositeBoundaryFrame_functional_coordinate]
  exact pullback.condition

end AlgebraicGeometry.Scheme.Hom
