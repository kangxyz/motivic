/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.FullBoundaryCoordinate
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.FullBoundaryProduct
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.PrescribedPairPullback
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTensor.Product

/-! # The original graph-twisted section pair agrees on infinity

The prescribed numerator and the graph-twisted original pole have the same
literal restriction to the whole infinity scheme. No sections are reselected.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.GraphInfinityEquality`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.PrescribedGraphRatio`,
`Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.Norm.GraphTwistedPoleCorrespondence`,
`Motivic.Transfers.Presheaf.Actions.Pencils.GraphBoundary`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- A prescribed inverse frame equals the canonical divisor section wherever its
actual coordinate is one. This compares sections, rather than divisor classes. -/
theorem prescribed_pair_eq_twistedIdealSection {X W : Scheme.{u}} (f : W ⟶ X)
    (I T : LineBundle X) (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      (tensorLineBundle X T (dualLineBundle X I)).val)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
    (E : (Modules.pullback f).obj (dualLineBundle X I).val ≅
      SheafOfModules.unit W.ringCatSheaf)
    (ha : pullbackSectionMap f a ≫ pullbackTensorMap f T.val (dualLineBundle X I).val =
      tensorUnitSection (pullbackSectionMap f b) E.inv)
    (hE : pullbackSectionMap f (canonicalDualHom X I.val φ) ≫ E.hom = 𝟙 _) :
    pullbackSectionMap f a =
      pullbackSectionMap f (twistedIdealSection X I T φ b) := by
  have : IsIso (pullbackTensorMap f T.val (dualLineBundle X I).val) :=
    PullbackTensor.Local.pullbackTensorMap_isIso f T.val (dualLineBundle X I).val T.property
  have hc : pullbackSectionMap f (canonicalDualHom X I.val φ) = E.inv := by
    apply (cancel_mono E.hom).mp
    rw [hE, Iso.inv_hom_id]
  apply (cancel_mono (pullbackTensorMap f T.val (dualLineBundle X I).val)).mp
  rw [ha]
  exact ((pullbackSectionMap_tensorUnitSection f b (canonicalDualHom X I.val φ)).trans
    (congrArg (tensorUnitSection (pullbackSectionMap f b)) hc)).symm

end AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S X Y Z C D : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (π : C ⟶ S) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ π = p ≫ q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))
  (T : LineBundle (pullback (j ≫ π) π))
  (aS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))).val)
  (bS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ T.val)
  (hA : pullbackSectionMap (Hom.fullBoundaryProductMap π j d s) aS ≫
      pullbackTensorMap (Hom.fullBoundaryProductMap π j d s) T.val
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)).val =
    tensorUnitSection (pullbackSectionMap (Hom.fullBoundaryProductMap π j d s) bS)
      (Hom.relativeFullBoundaryFrame q π j p hq z s hs H e d hd).inv)

include hA in
/-- The exact sections selected for lambda agree at infinity after multiplying
the original pole section by the original graph section. -/
theorem graphSections_infinity_eq :
    pullbackSectionMap (Hom.infinityProductMap π j d) aS =
      pullbackSectionMap (Hom.infinityProductMap π j d)
        (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) T
          (Hom.idealInclusion (Hom.compactificationGraph π j)) bS) := by
  let E := Hom.relativeFullBoundaryFrame q π j p hq z s hs H e d hd
  have ha := prescribed_pair_pullback coprod.inl (Hom.fullBoundaryProductMap π j d s)
    T.val (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)).val E aS bS hA
  have hc := compositeBoundaryFrame_coordinate coprod.inl
    (Hom.fullBoundaryProductMap π j d s)
    (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)).val E
    (canonicalDualHom _ (Hom.relativeCompactificationGraphLine π j).val
      (Hom.idealInclusion (Hom.compactificationGraph π j)))
  have hi := Hom.relativeFullBoundaryCoordinate_inl q π j p hq z s hs H e d hd
  have hcoord : _ = 𝟙 _ := hc.trans hi
  have he := prescribed_pair_eq_twistedIdealSection
    (coprod.inl ≫ Hom.fullBoundaryProductMap π j d s)
    (Hom.relativeCompactificationGraphLine π j) T
    (Hom.idealInclusion (Hom.compactificationGraph π j)) aS bS
    (compositeBoundaryFrame coprod.inl (Hom.fullBoundaryProductMap π j d s)
      (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)).val E) ha hcoord
  dsimp only [Hom.fullBoundaryProductMap] at he
  rw [coprod.inl_desc] at he
  exact he

include hA in
/-- The common infinity value is a unit because the original numerator is a unit
on its entire prescribed boundary. The graph-twisted pole is not reselected. -/
theorem graphTwistedSection_infinity_isIso
    [IsIso (pullbackSectionMap (Hom.fullBoundaryProductMap π j d s) aS)] :
    IsIso (pullbackSectionMap (Hom.infinityProductMap π j d)
      (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) T
        (Hom.idealInclusion (Hom.compactificationGraph π j)) bS)) := by
  rw [← graphSections_infinity_eq q π j p hq z s hs H e d hd T aS bS hA]
  have : IsIso (pullbackSectionMap
      (coprod.inl ≫ Hom.fullBoundaryProductMap π j d s) aS) := by
    rw [← pullbackSectionMap_comp]
    have : IsIso (pullbackSectionMap coprod.inl
        (pullbackSectionMap (Hom.fullBoundaryProductMap π j d s) aS)) := by
      change IsIso ((pullbackUnitIso coprod.inl).inv ≫
        (Modules.pullback coprod.inl).map
          (pullbackSectionMap (Hom.fullBoundaryProductMap π j d s) aS))
      infer_instance
    infer_instance
  dsimp only [Hom.fullBoundaryProductMap] at this
  rw [coprod.inl_desc] at this
  exact this

include hA in
/-- The infinity equality retains the actual dual functionals used by the
polynomial pencil on the enlarged retained open. -/
theorem graphFunctionals_infinity_eq :
    Hom.pullbackToUnit
        (sectionDualFunctional _
          (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)))
          aS) (Hom.infinityProductMap π j d) =
      Hom.pullbackToUnit
        (sectionDualFunctional _
          (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)))
          (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) T
            (Hom.idealInclusion (Hom.compactificationGraph π j)) bS))
        (Hom.infinityProductMap π j d) := by
  have he := graphSections_infinity_eq q π j p hq z s hs H e d hd T aS bS hA
  rw [sectionDualFunctional_pullback, sectionDualFunctional_pullback]
  simp only [pulledSectionDualFunctional, he]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
