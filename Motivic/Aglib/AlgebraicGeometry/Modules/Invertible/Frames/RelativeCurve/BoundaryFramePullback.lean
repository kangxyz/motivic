module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.BoundaryFrame
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateUnitOnOpen
/-! # A genuine relative-curve boundary frame pulls back with its literal scalar

The target frame is the actual graph ideal frame constructed locally in BoundaryFrame.
No polynomial coordinate or reduced boundary is used in this transport.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Y Z : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (p : Y ⟶ X) [Flat p]
  (z : Z ⟶ X) (s : Z ⟶ Y) (h : s ≫ p = z)
  (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget q z))

/-- Pullback of the specified actual ideal frame through the full Cartesian boundary. -/
def relativeNeighborhoodBoundaryFrame :
    SheafOfModules.unit (pullback (p ≫ q) (z ≫ q)).ringCatSheaf ≅
      idealModule (boundaryGraphSource q p z s h) := by
  have := relativeBoundaryGraph_closed q z
  have : (idealModule (boundaryGraphTarget q z)).IsQuasicoherent := by
    have := finiteLocallyFree_of_isLocallyRankOne (relativeBoundaryGraphLine q z).val
      (relativeBoundaryGraphLine q z).property
    exact inferInstanceAs ((relativeBoundaryGraphLine q z).val.IsQuasicoherent)
  have : IsClosedImmersion (boundaryGraphSource q p z s h) :=
    MorphismProperty.of_isPullback (boundaryGraph_isPullback q p z s h H) inferInstance
  let v := idealPullbackMap (boundaryGraphTarget q z) (boundaryGraphSource q p z s h)
    (boundaryProductMap q p z) (𝟙 Z) (boundaryGraph_isPullback q p z s h H).w
  have : IsIso v := boundaryGraph_idealPullbackMap_isIso q p z s h H
  exact (pullbackUnitIso (boundaryProductMap q p z)).symm ≪≫
    (Scheme.Modules.pullback (boundaryProductMap q p z)).mapIso e ≪≫ asIso v

/-- The scalar is precisely the pulled original scalar, not just another unit frame. -/
@[reassoc]
theorem relativeNeighborhoodBoundaryFrame_inclusion :
    (relativeNeighborhoodBoundaryFrame q p z s h H e).hom ≫
        idealInclusion (boundaryGraphSource q p z s h) =
      unitEndomorphismPullback (boundaryProductMap q p z)
        (e.hom ≫ idealInclusion (boundaryGraphTarget q z)) := by
  simp only [relativeNeighborhoodBoundaryFrame, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_hom, Category.assoc,
    unitEndomorphismPullback, Functor.map_comp]
  rw [idealPullbackMap_inclusion]
  rfl
end AlgebraicGeometry.Scheme.Hom
