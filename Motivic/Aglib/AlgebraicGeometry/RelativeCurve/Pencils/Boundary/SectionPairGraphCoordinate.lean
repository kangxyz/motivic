/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.NormalizedTwistedIdealCoordinate
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.PrescribedGraphRatio
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.IdealFrameBoundaryScalar

/-! # Boundary coordinates of the ideal frame induced by the original section pair

The same chosen numerator and untwisted pole determine the frame on their unit
domain. Their original prescribed equation computes the graph coefficient on
the whole nonreduced boundary. The graph-twisted pole itself is not inverted.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairGraphCoordinate`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.RetainedSectionPairCoefficient`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairGraphInfinityNorm`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairGraphMarkedNorm`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
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

variable {W : Scheme.{u}} (w : W ⟶ pullback (j ≫ π) π)
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _ T bS) w)]
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _
    (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))) aS) w)]

/-- The graph coefficient in the deterministic frame from the same original pair. -/
def sectionPairGraphCoefficient :
    SheafOfModules.unit W.ringCatSheaf ⟶ SheafOfModules.unit W.ringCatSheaf :=
  (sectionPairIdealFrame w (Hom.relativeCompactificationGraphLine π j) T bS aS).inv ≫
    Hom.pullbackToUnit (Hom.idealInclusion (Hom.compactificationGraph π j)) w

include hA in
/-- The entire original prescribed boundary computes this coefficient, including
its graph zeros. Only the original numerator and untwisted pole are units. -/
theorem sectionPairGraphCoefficient_boundary {B : Scheme.{u}}
    (r : B ⟶ W)
    (v : B ⟶ (pullback (pullback.snd (j ≫ π) π) d ⨿ pullback (j ≫ π) (s ≫ j ≫ π)))
    (h : r ≫ w = v ≫ Hom.fullBoundaryProductMap π j d s) :
    Hom.unitEndomorphismPullback r (sectionPairGraphCoefficient π j T aS bS w) =
      Hom.unitEndomorphismPullback v
        (Hom.relativeFullBoundaryCoordinate q π j p hq z s hs H e d hd) := by
  have hfull := prescribed_pair_twistedIdealSection_eq_coordinate
    (Hom.fullBoundaryProductMap π j d s) (Hom.relativeCompactificationGraphLine π j) T
    (Hom.idealInclusion (Hom.compactificationGraph π j)) aS bS
    (Hom.relativeFullBoundaryFrame q π j p hq z s hs H e d hd) hA
  exact sectionPairIdealFrame_graphCoefficient_boundary_of_factorization
    w (Hom.relativeCompactificationGraphLine π j) T bS aS
    (Hom.fullBoundaryProductMap π j d s) r v h
    (Hom.idealInclusion (Hom.compactificationGraph π j))
    (Hom.relativeFullBoundaryCoordinate q π j p hq z s hs H e d hd) hfull

include hA in
/-- The actual marked value retains the same supplied ideal frame. -/
theorem sectionPairGraphCoefficient_marked_scalar {B : Scheme.{u}}
    (r : B ⟶ W) (v : B ⟶ pullback (j ≫ π) (s ≫ j ≫ π))
    (h : r ≫ w = v ≫ Hom.graphBoundaryRestriction π j s) :
    r.appTop (Modules.Hom.app (sectionPairGraphCoefficient π j T aS bS w) ⊤ (1 : Γ(W, ⊤))) =
      Modules.Hom.app (Hom.unitEndomorphismPullback
        (v ≫ (Hom.relativeBoundaryProductIso q π j p hq z s hs).hom ≫
          Hom.boundaryProductMap q p z)
        (e.hom ≫ Hom.idealInclusion (Hom.boundaryGraphTarget q z))) ⊤ (1 : Γ(B, ⊤)) := by
  rw [← Hom.unitEndomorphismPullback_app_one]
  have hh := sectionPairGraphCoefficient_boundary q π j p hq z s hs H e d hd T aS bS hA
    w r (v ≫ coprod.inr) (by simpa [Hom.fullBoundaryProductMap] using h)
  rw [hh, ← Hom.unitEndomorphismPullback_comp, Hom.relativeFullBoundaryCoordinate_inr,
    Hom.unitEndomorphismPullback_comp]

include hA in
/-- Actual factorization through the full chosen infinity gives one, including
all residual nilpotents retained in the thickened boundary. -/
theorem sectionPairGraphCoefficient_infinity_scalar {B : Scheme.{u}}
    (r : B ⟶ W) (v : B ⟶ pullback (pullback.snd (j ≫ π) π) d)
    (h : r ≫ w = v ≫ Hom.infinityProductMap π j d) :
    r.appTop (Modules.Hom.app (sectionPairGraphCoefficient π j T aS bS w) ⊤ (1 : Γ(W, ⊤))) =
      1 := by
  rw [← Hom.unitEndomorphismPullback_app_one]
  have hh := sectionPairGraphCoefficient_boundary q π j p hq z s hs H e d hd T aS bS hA
    w r (v ≫ coprod.inl) (by simpa [Hom.fullBoundaryProductMap] using h)
  rw [hh, ← Hom.unitEndomorphismPullback_comp, Hom.relativeFullBoundaryCoordinate_inl]
  rw [Hom.unitEndomorphismPullback_app_one]
  change v.appTop (1 : Γ(pullback (pullback.snd (j ≫ π) π) d, ⊤)) = 1
  exact map_one v.appTop.hom

end AlgebraicGeometry.Scheme.RelativeCurvePencil
