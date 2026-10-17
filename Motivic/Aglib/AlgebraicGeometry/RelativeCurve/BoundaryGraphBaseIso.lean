module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryBaseCanonicalFrame
/-! # Literal boundary graph frames under an isomorphism of bases -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S T X Z : Scheme.{u}} (q : X ⟶ S) (z : Z ⟶ X) (e : S ≅ T)

/-- The canonical products before and after presenting an affine base as its spectrum. -/
def boundaryGraphBaseIso :
    pullback (q ≫ e.hom) (z ≫ q ≫ e.hom) ≅ pullback q (z ≫ q) where
  hom := pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
    apply (cancel_mono e.hom).mp
    simpa only [Category.assoc] using pullback.condition (f := q ≫ e.hom)
      (g := z ≫ q ≫ e.hom))
  inv := pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
    simpa only [Category.assoc] using congrArg (fun f => f ≫ e.hom)
      (pullback.condition (f := q) (g := z ≫ q)))
  hom_inv_id := by apply pullback.hom_ext <;> simp
  inv_hom_id := by apply pullback.hom_ext <;> simp

@[reassoc (attr := simp)]
theorem boundaryGraphBaseIso_hom_fst :
    (boundaryGraphBaseIso q z e).hom ≫ pullback.fst q (z ≫ q) = pullback.fst _ _ :=
  pullback.lift_fst _ _ _
@[reassoc (attr := simp)]
theorem boundaryGraphBaseIso_hom_snd :
    (boundaryGraphBaseIso q z e).hom ≫ pullback.snd q (z ≫ q) = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- Equality of the original canonical graph maps, not just their divisor classes. -/
@[reassoc]
theorem boundaryGraphBaseIso_graph :
    boundaryGraphTarget (q ≫ e.hom) z ≫ (boundaryGraphBaseIso q z e).hom =
      boundaryGraphTarget q z := by
  apply pullback.hom_ext <;> simp [boundaryGraphTarget]

theorem boundaryGraphBaseIso_isPullback :
    IsPullback (𝟙 Z) (boundaryGraphTarget (q ≫ e.hom) z)
      (boundaryGraphTarget q z) (boundaryGraphBaseIso q z e).hom :=
  IsPullback.of_horiz_isIso ⟨by simp [boundaryGraphBaseIso_graph]⟩

variable [IsSeparated q] [SmoothOfRelativeDimension 1 q]

/-- The given frame is transported through the original ideal pullback map. -/
def boundaryGraphFrame_baseIso
    (a : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
      idealModule (boundaryGraphTarget q z)) :
    SheafOfModules.unit (pullback (q ≫ e.hom) (z ≫ q ≫ e.hom)).ringCatSheaf ≅
      idealModule (boundaryGraphTarget (q ≫ e.hom) z) := by
  have := relativeBoundaryGraph_closed q z
  have : (idealModule (boundaryGraphTarget q z)).IsQuasicoherent := by
    have := finiteLocallyFree_of_isLocallyRankOne (relativeBoundaryGraphLine q z).val
      (relativeBoundaryGraphLine q z).property
    exact inferInstanceAs ((relativeBoundaryGraphLine q z).val.IsQuasicoherent)
  let H := boundaryGraphBaseIso_isPullback q z e
  have : IsClosedImmersion (boundaryGraphTarget (q ≫ e.hom) z) :=
    MorphismProperty.of_isPullback H inferInstance
  let v := idealPullbackMap (boundaryGraphTarget q z)
    (boundaryGraphTarget (q ≫ e.hom) z) (boundaryGraphBaseIso q z e).hom (𝟙 Z) H.w
  have : IsIso v := idealPullbackMap_isIso_of_flat_ambient _ _ _ _ _ H
  exact (pullbackUnitIso (boundaryGraphBaseIso q z e).hom).symm ≪≫
    (Modules.pullback (boundaryGraphBaseIso q z e).hom).mapIso a ≪≫ asIso v

@[reassoc]
theorem boundaryGraphFrame_baseIso_inclusion
    (a : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
      idealModule (boundaryGraphTarget q z)) :
    (boundaryGraphFrame_baseIso q z e a).hom ≫
      idealInclusion (boundaryGraphTarget (q ≫ e.hom) z) =
    (pullbackUnitIso (boundaryGraphBaseIso q z e).hom).inv ≫
      (Modules.pullback (boundaryGraphBaseIso q z e).hom).map a.hom ≫
      Modules.Hom.pullbackToUnit (idealInclusion (boundaryGraphTarget q z))
        (boundaryGraphBaseIso q z e).hom := by
  simp only [boundaryGraphFrame_baseIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_hom, Category.assoc]
  rw [idealPullbackMap_inclusion]
  rfl
end AlgebraicGeometry.Scheme.Hom
