/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.RetainedSectionPairCoefficient
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.RetainedMarkedCoordinateComparison

/-! # The original target section-pair scalar at the actual marked chart point

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairNativeTargetScalar`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Norm.SectionPairBoundaryEquality`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S X Y Z C P D W B : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (π : P ⟶ S) [IsSeparated π]
  (f : C ⟶ P) (jB : Y ⟶ C) (jA : X ⟶ P) [IsOpenImmersion jA]
  [SmoothOfRelativeDimension 1 (jA ≫ π)] (p : Y ⟶ X)
  (hret : jB ≫ f = p ≫ jA) (hA : jA ≫ π = q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (d : D ⟶ P) (hd : Disjoint (Set.range jA) (Set.range d))
  (L : LineBundle (pullback (jA ≫ π) π))
  (aS : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ L (dualLineBundle _
      (Hom.relativeCompactificationGraphLine π jA))).val)
  (bS : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶ L.val)
  (hpair : pullbackSectionMap (Hom.fullBoundaryProductMap π jA d z) aS ≫
      pullbackTensorMap (Hom.fullBoundaryProductMap π jA d z) L.val
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)).val =
    tensorUnitSection (pullbackSectionMap (Hom.fullBoundaryProductMap π jA d z) bS)
      (Hom.relativeFullBoundaryFrame q π jA (𝟙 X) (hA.trans (Category.id_comp q).symm)
        z z (Category.comp_id z) (IsPullback.id_vert z) e d hd).inv)
  (v : W ⟶ pullback (jA ≫ π) π)
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _ L bS) v)]
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _
    (tensorLineBundle _ L (dualLineBundle _
      (Hom.relativeCompactificationGraphLine π jA))) aS) v)]
  (γ : B ⟶ pullback (jB ≫ f ≫ π) (f ≫ π)) (a : B ⟶ Z)
  (hp : γ ≫ pullback.snd (jB ≫ f ≫ π) (f ≫ π) = a ≫ s ≫ jB)
  (r : B ⟶ W)
  (hr : r ≫ v = Hom.retainedMarkedTargetAmbient π f jB jA p hret γ)

include hpair hr in
/-- The original target pair evaluates to the unchanged supplied marked frame.
The marked factor is constructed from the same original source chart point. -/
theorem sectionPairGraphCoefficient_native_target_marked_value :
    r.appTop (Modules.Hom.app (sectionPairGraphCoefficient π jA L aS bS v) ⊤
      (1 : Γ(W, ⊤))) =
    Modules.Hom.app (Hom.unitEndomorphismPullback
      (Hom.retainedNativeTargetMarkedFactor π f jB jA p hret z s hs γ a hp ≫
        (Hom.relativeBoundaryProductIso q π jA (𝟙 X) (hA.trans (Category.id_comp q).symm)
          z z (Category.comp_id z)).hom ≫ Hom.boundaryProductMap q (𝟙 X) z)
      (e.hom ≫ Hom.idealInclusion (Hom.boundaryGraphTarget q z))) ⊤ (1 : Γ(B, ⊤)) := by
  apply sectionPairGraphCoefficient_marked_scalar q π jA (𝟙 X)
    (hA.trans (Category.id_comp q).symm) z z (Category.comp_id z) (IsPullback.id_vert z) e d hd
    L aS bS hpair v r
    (Hom.retainedNativeTargetMarkedFactor π f jB jA p hret z s hs γ a hp)
  exact hr.trans (IsPullback.lift_fst _ _ _ _).symm

include hpair in
/-- On the actual inverse target chart, the ambient factor equation follows from
its projections and the original finite graph-product square. -/
theorem sectionPairGraphCoefficient_actual_target_chart_marked_value
    {T W' : Scheme.{u}}
    (vB : T ⟶ pullback (jB ≫ f ≫ π) (f ≫ π)) (n : T ⟶ W')
    (w : W' ⟶ pullback (jB ≫ f ≫ π) π)
    (hn : vB ≫ Hom.graphProductMap π f jB = n ≫ w)
    (l : W' ⟶ pullback (Hom.retainedParameterProductMap π f jB jA p hret) v)
    (hl : l ≫ pullback.fst (Hom.retainedParameterProductMap π f jB jA p hret) v = w)
    (δ : B ⟶ T) (a : B ⟶ Z)
    (hp : (δ ≫ vB) ≫ pullback.snd (jB ≫ f ≫ π) (f ≫ π) = a ≫ s ≫ jB) :
    (δ ≫ n ≫ l ≫ pullback.snd (Hom.retainedParameterProductMap π f jB jA p hret) v).appTop
      (Modules.Hom.app (sectionPairGraphCoefficient π jA L aS bS v) ⊤ (1 : Γ(W, ⊤))) =
    Modules.Hom.app (Hom.unitEndomorphismPullback
      (Hom.retainedNativeTargetMarkedFactor π f jB jA p hret z s hs (δ ≫ vB) a hp ≫
        (Hom.relativeBoundaryProductIso q π jA (𝟙 X) (hA.trans (Category.id_comp q).symm)
          z z (Category.comp_id z)).hom ≫ Hom.boundaryProductMap q (𝟙 X) z)
      (e.hom ≫ Hom.idealInclusion (Hom.boundaryGraphTarget q z))) ⊤ (1 : Γ(B, ⊤)) := by
  apply sectionPairGraphCoefficient_native_target_marked_value q π f jB jA p hret hA
    z s hs e d hd L aS bS hpair v (δ ≫ vB) a hp
    (δ ≫ n ≫ l ≫ pullback.snd (Hom.retainedParameterProductMap π f jB jA p hret) v)
  simpa only [Category.assoc] using
    Hom.retainedMarkedChart_ambient π f jB jA p hret vB n w hn v l hl δ

end AlgebraicGeometry.Scheme.RelativeCurvePencil
