module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.BoundaryFramePullback
/-! # The original compactification graph inherits a prescribed relative-curve frame -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Y Z C : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (qC : C ⟶ S) [IsSeparated qC]
  (j : Y ⟶ C) [IsOpenImmersion j] (p : Y ⟶ X) [Flat p]
  (hq : j ≫ qC = p ≫ q) (z : Z ⟶ X) (s : Z ⟶ Y) (h : s ≫ p = z)
  (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget q z))

/-- Literal product comparison; neither the boundary nor the original compactification changes. -/
def relativeBoundaryProductIso :
    pullback (j ≫ qC) (s ≫ j ≫ qC) ≅ pullback (p ≫ q) (z ≫ q) :=
  pullback.congrHom hq (by rw [hq, ← Category.assoc, h])

/-- The frame of the original compactification ideal, transported through actual ideal maps. -/
def relativeCompactificationBoundaryFrame :
    SheafOfModules.unit (pullback (j ≫ qC) (s ≫ j ≫ qC)).ringCatSheaf ≅
      (Scheme.Modules.pullback (graphBoundaryRestriction qC j s)).obj
        (idealModule (compactificationGraph qC j)) := by
  let eP := relativeBoundaryProductIso q qC j p hq z s h
  have he : 𝟙 Z ≫ boundaryGraphSource q p z s h =
      restrictedBoundaryGraph qC j s ≫ eP.hom := by
    apply pullback.hom_ext <;>
      simp [eP, relativeBoundaryProductIso, pullback.congrHom,
        boundaryGraphSource, restrictedBoundaryGraph]
  let v := idealPullbackMap (boundaryGraphSource q p z s h)
    (restrictedBoundaryGraph qC j s) eP.hom (𝟙 Z) he
  have : IsIso v := idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  have : IsClosedImmersion (compactificationGraph qC j) := by
    dsimp [compactificationGraph]
    infer_instance
  let w := idealPullbackMap (compactificationGraph qC j) (restrictedBoundaryGraph qC j s)
    (graphBoundaryRestriction qC j s) s (compactificationGraph_boundary_isPullback qC j s).w
  have : IsIso w := compactificationGraph_boundaryIdealMap_isIso qC j s
  exact (pullbackUnitIso eP.hom).symm ≪≫
    (Scheme.Modules.pullback eP.hom).mapIso (relativeNeighborhoodBoundaryFrame q p z s h H e) ≪≫
      asIso v ≪≫ (asIso w).symm

/-- The canonical graph section has exactly the pulled target-curve scalar in this frame. -/
theorem relativeCompactificationBoundaryFrame_coordinate :
    (relativeCompactificationBoundaryFrame q qC j p hq z s h H e).hom ≫
      Modules.Hom.pullbackToUnit (idealInclusion (compactificationGraph qC j))
        (graphBoundaryRestriction qC j s) =
      unitEndomorphismPullback
        ((relativeBoundaryProductIso q qC j p hq z s h).hom ≫ boundaryProductMap q p z)
        (e.hom ≫ idealInclusion (boundaryGraphTarget q z)) := by
  have hcoord := relativeNeighborhoodBoundaryFrame_inclusion q p z s h H e
  rw [← unitEndomorphismPullback_comp, ← hcoord]
  dsimp only [relativeCompactificationBoundaryFrame, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_hom, asIso_inv]
  simp only [Category.assoc]
  unfold Modules.Hom.pullbackToUnit
  erw [← idealPullbackMap_inclusion (compactificationGraph qC j)
    (restrictedBoundaryGraph qC j s) (graphBoundaryRestriction qC j s) s
    (compactificationGraph_boundary_isPullback qC j s).w]
  rw [IsIso.inv_hom_id_assoc, idealPullbackMap_inclusion]
  simp only [unitEndomorphismPullback, Functor.map_comp, Category.assoc]
  rfl
end AlgebraicGeometry.Scheme.Hom
