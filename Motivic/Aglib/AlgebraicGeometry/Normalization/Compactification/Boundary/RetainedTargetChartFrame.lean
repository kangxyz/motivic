/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RetainedParameterGraph
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.CompositeFrameFunctional

/-! # The same prescribed target frame on the original retained graph chart

The original retained commutation, not a replacement graph, determines the
ideal comparison. The existing target extension frame is pulled along the
literal inverse-chart projection and keeps its exact functional coordinate.


Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RetainedTargetChartFrame`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.RetainedTargetPrescribedScalar`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.RetainedSectionPairCoefficient`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S C P X Y W : Scheme.{u}} (q : P ⟶ S) (f : C ⟶ P)
  (jB : Y ⟶ C) (jA : X ⟶ P) (p : Y ⟶ X) (h : jB ≫ f = p ≫ jA) [Flat p]
  [IsClosedImmersion (compactificationGraph q jA)]
  [IsClosedImmersion (targetCompactificationGraph q f jB)]
  (hI : IsLocallyRankOne _ (idealModule (compactificationGraph q jA)))
  (v : W ⟶ pullback (jA ≫ q) q)
  (e : (Modules.pullback v).obj (idealModule (compactificationGraph q jA)) ≅
    SheafOfModules.unit W.ringCatSheaf)

/-- The SAME original target frame, pulled to the literal inverse chart. -/
def retainedTargetChartFrame :
    (Modules.pullback (pullback.fst (retainedParameterProductMap q f jB jA p h) v)).obj
      (idealModule (targetCompactificationGraph q f jB)) ≅
        SheafOfModules.unit (pullback (retainedParameterProductMap q f jB jA p h) v).ringCatSheaf :=
  (Modules.pullback (pullback.fst (retainedParameterProductMap q f jB jA p h) v)).mapIso
      (retainedParameterGraphIdealIso q f jB jA p h hI).symm ≪≫
    (Modules.pullbackComp (pullback.fst (retainedParameterProductMap q f jB jA p h) v)
      (retainedParameterProductMap q f jB jA p h)).app (idealModule (compactificationGraph q jA)) ≪≫
    (Modules.pullbackCongr
      (pullback.condition (f := retainedParameterProductMap q f jB jA p h) (g := v))).app
      (idealModule (compactificationGraph q jA)) ≪≫
    compositeBoundaryFrame (pullback.snd (retainedParameterProductMap q f jB jA p h) v) v
      (idealModule (compactificationGraph q jA)) e

/-- The actual pulled target coordinate is exactly the same functional coordinate,
not merely an associated graph generator. -/
theorem retainedTargetChartFrame_coordinate :
    (retainedTargetChartFrame q f jB jA p h hI v e).inv ≫
      pullbackUnitMap (pullback.fst (retainedParameterProductMap q f jB jA p h) v)
        (idealInclusion (targetCompactificationGraph q f jB)) =
    unitEndomorphismPullback (pullback.snd (retainedParameterProductMap q f jB jA p h) v)
      (e.inv ≫ pullbackUnitMap v (idealInclusion (compactificationGraph q jA))) := by
  have hi :
      (Modules.pullback (pullback.fst (retainedParameterProductMap q f jB jA p h) v)).map
          (retainedParameterGraphIdealIso q f jB jA p h hI).hom ≫
        pullbackUnitMap (pullback.fst (retainedParameterProductMap q f jB jA p h) v)
          (idealInclusion (targetCompactificationGraph q f jB)) =
      pullbackUnitMap (pullback.fst (retainedParameterProductMap q f jB jA p h) v)
        (pullbackUnitMap (retainedParameterProductMap q f jB jA p h)
          (idealInclusion (compactificationGraph q jA))) := by
    dsimp only [pullbackUnitMap]
    rw [← Functor.map_comp_assoc, retainedParameterGraphIdealIso_inclusion]
    rfl
  simp only [retainedTargetChartFrame, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Category.assoc]
  rw [hi, ← pullbackUnitMap_comp, Iso.inv_hom_id_assoc,
    ← pullbackUnitMap_congr, Iso.inv_hom_id_assoc,
    compositeBoundaryFrame_functional_coordinate]
  exact pullback.condition

end AlgebraicGeometry.Scheme.Hom
