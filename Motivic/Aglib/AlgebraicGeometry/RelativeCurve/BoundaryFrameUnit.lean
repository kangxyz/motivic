module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryFramePullback
/-! # The original relative boundary scalar is a unit on the punctured source -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X A Z : Scheme.{u}} (q : X ⟶ S) (a : A ⟶ X) (z : Z ⟶ X)

/-- Disjointness from the full boundary makes the original graph pullback empty. -/
theorem relativeBoundaryGraph_pullback_isEmpty
    (h : Disjoint (Set.range a) (Set.range z)) :
    IsEmpty (pullback (C := Scheme) (boundaryGraphTarget q z) (boundaryProductMap q a z)) := by
  apply Scheme.isEmpty_pullback
  apply Set.disjoint_left.mpr
  rintro x ⟨t, rfl⟩ ⟨b, hb⟩
  have he : a ((pullback.fst (a ≫ q) (z ≫ q)) b) = z t := by
    have he := congrArg (fun v => (pullback.fst q (z ≫ q)) v) hb
    change (boundaryProductMap q a z ≫ pullback.fst q (z ≫ q)) b =
      (boundaryGraphTarget q z ≫ pullback.fst q (z ≫ q)) t at he
    simpa only [boundaryProductMap, boundaryGraphTarget, pullback.lift_fst,
      Scheme.Hom.comp_apply] using he
  exact Set.disjoint_iff_forall_ne.mp h ⟨_, rfl⟩ ⟨t, rfl⟩ he

/-- The exact scalar specified by the target ideal frame becomes a unit, without a new choice. -/
theorem relativeBoundaryFrame_scalar_isIso [IsSeparated q] [Flat a]
    (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
      idealModule (boundaryGraphTarget q z))
    (h : Disjoint (Set.range a) (Set.range z)) :
    IsIso (unitEndomorphismPullback (boundaryProductMap q a z)
      (e.hom ≫ idealInclusion (boundaryGraphTarget q z))) := by
  let i := boundaryGraphTarget q z
  let b := boundaryProductMap q a z
  let i' := pullback.snd i b
  have : IsClosedImmersion i := relativeBoundaryGraph_closed q z
  let := Scheme.Modules.unit_isLocallyFree (pullback q (z ≫ q))
  have : (idealModule i).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent _).prop_of_iso e inferInstance
  have : IsEmpty (pullback (C := Scheme) i b) := relativeBoundaryGraph_pullback_isEmpty q a z h
  have : IsIso (idealInclusion i') := idealInclusion_isIso_of_isEmpty i'
  have : IsIso (idealPullbackMap i i' b (pullback.fst i b) pullback.condition) :=
    idealPullbackMap_isIso_of_flat_ambient _ _ _ _ _ (IsPullback.of_hasPullback _ _)
  have hi : IsIso (Modules.Hom.pullbackToUnit (idealInclusion i) b) := by
    change IsIso ((Scheme.Modules.pullback b).map (idealInclusion i) ≫
      SheafOfModules.pullbackObjUnitToUnit b.toRingCatSheafHom)
    rw [← idealPullbackMap_inclusion i i' b (pullback.fst i b) pullback.condition]
    infer_instance
  change IsIso ((pullbackUnitIso b).inv ≫ (Scheme.Modules.pullback b).map
    (e.hom ≫ idealInclusion i) ≫ (pullbackUnitIso b).hom)
  rw [Functor.map_comp, Category.assoc]
  change IsIso ((pullbackUnitIso b).inv ≫ (Scheme.Modules.pullback b).map e.hom ≫
    Modules.Hom.pullbackToUnit (idealInclusion i) b)
  infer_instance
end AlgebraicGeometry.Scheme.Hom
