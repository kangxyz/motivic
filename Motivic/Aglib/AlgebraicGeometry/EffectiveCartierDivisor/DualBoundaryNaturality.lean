/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.EtaleBoundaryIdeal
public import Motivic.Aglib.AlgebraicGeometry.Modules.Pullback.PullbackTensorComposition
public import Motivic.Aglib.AlgebraicGeometry.Modules.Pullback.RightUnit
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.DisjointBoundary.Restriction
public import Aglib.AlgebraicGeometry.Modules.Restriction.Unit

/-! # Naturality of the specified ideal frame's dual

These identities use the full evaluation pairing. They do not cancel a canonical
section, which can vanish along the graph.


Intended upstream module: `Aglib.AlgebraicGeometry.EffectiveCartierDivisor.DualBoundaryNaturality`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.CoherentIdealFrame`.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- Evaluation determines the dual frame on the entire pulled-back ideal line. -/
theorem dualBoundaryTrivialization_pairing {X W : Scheme.{u}} (f : W ⟶ X)
    (L : LineBundle X)
    (e : SheafOfModules.unit W.ringCatSheaf ≅ (Modules.pullback f).obj L.val) :
    tensorSheafMap W (𝟙 ((Modules.pullback f).obj (dualLineBundle X L).val)) e.inv ≫
      (tensorSheafRightUnit W _).hom ≫ (dualBoundaryTrivialization f L e).hom =
    (PullbackTensor.Local.pullbackLineBundleTensorIso f (dualLineBundle X L) L).inv ≫
      (Modules.pullback f).map (dualEvaluationIso X L).hom ≫ (pullbackUnitIso f).hom := by
  change (tensorSheafIso W (Iso.refl _) e.symm).hom ≫
    (tensorSheafRightUnit W _).hom ≫ (tensorSheafRightUnit W _).inv ≫
      (tensorSheafIso W (Iso.refl _) e).hom ≫ _ = _
  simp only [Iso.hom_inv_id_assoc]
  change (tensorSheafIso W (Iso.refl _) e).inv ≫
    (tensorSheafIso W (Iso.refl _) e).hom ≫ _ = _
  simp only [Iso.inv_hom_id_assoc]
  rfl

/-- Dualizing a specified ideal frame commutes with actual pullback composition. -/
theorem dualBoundaryTrivialization_comp {X W V : Scheme.{u}} (f : V ⟶ W) (g : W ⟶ X)
    (L : LineBundle X)
    (e : SheafOfModules.unit W.ringCatSheaf ≅ (Modules.pullback g).obj L.val) :
    dualBoundaryTrivialization (f ≫ g) L
      ((pullbackUnitIso f).symm ≪≫ (Modules.pullback f).mapIso e ≪≫
        (Modules.pullbackComp f g).app L.val) =
    ((Modules.pullbackComp f g).app (dualLineBundle X L).val).symm ≪≫
      (Modules.pullback f).mapIso (dualBoundaryTrivialization g L e) ≪≫
        pullbackUnitIso f := by
  let D := (dualLineBundle X L).val
  let F := Modules.pullback f
  let G := Modules.pullback g
  let e' := (pullbackUnitIso f).symm ≪≫ F.mapIso e ≪≫
    (Modules.pullbackComp f g).app L.val
  let t := PullbackTensor.Local.pullbackLineBundleTensorIso g (dualLineBundle X L) L
  let t' := PullbackTensor.Local.pullbackLineBundleTensorIso (f ≫ g) (dualLineBundle X L) L
  let r := tensorSheafRightUnit V (F.obj (G.obj D))
  let cD := (Modules.pullbackComp f g).app D
  let cI := (Modules.pullbackComp f g).app L.val
  let a := tensorSheafIso V (Iso.refl (F.obj (G.obj D)))
    ((F.mapIso e).symm ≪≫ pullbackUnitIso f)
  have ht : IsIso (pullbackTensorMap f (G.obj D) (G.obj L.val)) :=
    PullbackTensor.Local.pullbackTensorMap_isIso f _ _
      (pullback_locallyRankOne g D (dualLineBundle X L).property)
  apply Iso.ext
  apply (cancel_epi cD.hom).mp
  change cD.hom ≫ (dualBoundaryTrivialization (f ≫ g) L e').hom =
    cD.hom ≫ cD.inv ≫ F.map (dualBoundaryTrivialization g L e).hom ≫ (pullbackUnitIso f).hom
  rw [Iso.hom_inv_id_assoc]
  apply (cancel_epi (a.hom ≫ r.hom)).mp
  apply (cancel_epi (F.map t.hom ≫ pullbackTensorMap f (G.obj D) (G.obj L.val))).mp
  have hr := (SheafOfModulesOfCommRing.tensorRightUnitIso V.sheaf).hom.naturality cD.hom
  change tensorSheafMap V cD.hom (𝟙 _) ≫ (tensorSheafRightUnit V _).hom =
    r.hom ≫ cD.hom at hr
  have ha : a.hom ≫ tensorSheafMap V cD.hom (𝟙 _) =
      tensorSheafMap V cD.hom cI.hom ≫
        tensorSheafMap V (𝟙 _) e'.inv := by
    change tensorSheafMap V (𝟙 _) (F.map e.inv ≫ (pullbackUnitIso f).hom) ≫ _ = _
    rw [tensorSheafMap_comp, tensorSheafMap_comp]
    simp only [e', cI, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc,
      Category.id_comp, Category.comp_id, Iso.hom_inv_id_assoc]
  have hp := dualBoundaryTrivialization_pairing (f ≫ g) L e'
  have hg := dualBoundaryTrivialization_pairing g L e
  have hn := pullbackTensorMap_naturality f (𝟙 (G.obj D)) e.inv
  have hu := pullbackTensorMap_rightUnit f (G.obj D)
  have hc := pullbackTensorMap_comp f g D L.val
  change F.map t.hom ≫ pullbackTensorMap f (G.obj D) (G.obj L.val) ≫
    tensorSheafMap V cD.hom cI.hom =
      (Modules.pullbackComp f g).hom.app (tensorSheaf X D L.val) ≫ t'.hom at hc
  calc
    _ = F.map t.hom ≫ pullbackTensorMap f (G.obj D) (G.obj L.val) ≫
        tensorSheafMap V cD.hom cI.hom ≫ t'.inv ≫
          (Modules.pullback (f ≫ g)).map (dualEvaluationIso X L).hom ≫
            (pullbackUnitIso (f ≫ g)).hom := by
      simp only [Category.assoc]
      rw [← reassoc_of% hr, reassoc_of% ha]
      rw [hp]
    _ = F.map (G.map (dualEvaluationIso X L).hom) ≫
        F.map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom := by
      rw [reassoc_of% hc]
      simp only [Iso.hom_inv_id_assoc]
      rw [← reassoc_of% ((Modules.pullbackComp f g).hom.naturality (dualEvaluationIso X L).hom)]
      rw [pullbackUnitIso_comp]
    _ = F.map t.hom ≫ F.map (tensorSheafMap W (𝟙 (G.obj D)) e.inv) ≫
        F.map (tensorSheafRightUnit W (G.obj D)).hom ≫
          F.map (dualBoundaryTrivialization g L e).hom ≫ (pullbackUnitIso f).hom := by
      have hg' := congrArg (fun k => t.hom ≫ k) hg
      dsimp only [t] at hg'
      simp only [Iso.hom_inv_id_assoc] at hg'
      have hh := congrArg (fun k => F.map k ≫ (pullbackUnitIso f).hom) hg'
      simpa only [Functor.map_comp, Category.assoc] using hh.symm
    _ = _ := by
      simp only [Category.assoc]
      rw [← hu]
      simp only [Category.assoc]
      rw [reassoc_of% hn]
      rw [reassoc_of% tensorSheafMap_comp]
      rw [(Modules.pullback f).map_id (G.obj D)]
      simp only [Category.comp_id]
      rfl

/-- An actual open component retains the dual of its specified ideal frame.
The composition and open-unit comparisons are not suppressed. -/
theorem dualBoundaryTrivialization_restrict_of_inv {X W V : Scheme.{u}}
    (f : V ⟶ W) [IsOpenImmersion f] (g : W ⟶ X) (k : V ⟶ X) (h : f ≫ g = k)
    (L : LineBundle X)
    (e : SheafOfModules.unit W.ringCatSheaf ≅ (Modules.pullback g).obj L.val)
    (eV : SheafOfModules.unit V.ringCatSheaf ≅ (Modules.pullback k).obj L.val)
    (he : (Modules.restrictFunctor f).map e.inv ≫ (restrictUnitIso f).hom =
      (restrictFunctorIsoPullback f).hom.app ((Modules.pullback g).obj L.val) ≫
        (Modules.pullbackComp f g).hom.app L.val ≫
          (Modules.pullbackCongr h).hom.app L.val ≫ eV.inv) :
    (Modules.restrictFunctor f).map (dualBoundaryTrivialization g L e).hom ≫
        (restrictUnitIso f).hom =
      (restrictFunctorIsoPullback f).hom.app
          ((Modules.pullback g).obj (dualLineBundle X L).val) ≫
        (Modules.pullbackComp f g).hom.app (dualLineBundle X L).val ≫
          (Modules.pullbackCongr h).hom.app (dualLineBundle X L).val ≫
            (dualBoundaryTrivialization k L eV).hom := by
  subst k
  simp only [Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp] at he ⊢
  have hur : (restrictFunctorIsoPullback f).hom.app (SheafOfModules.unit W.ringCatSheaf) ≫
      (pullbackUnitIso f).hom = (restrictUnitIso f).hom :=
    restrictFunctorIsoPullback_hom_unit f
  let e' := (pullbackUnitIso f).symm ≪≫ (Modules.pullback f).mapIso e ≪≫
    (Modules.pullbackComp f g).app L.val
  have he' : e' = eV := by
    apply Iso.ext_inv
    apply (cancel_epi ((Modules.pullbackComp f g).hom.app L.val)).mp
    change (Modules.pullbackComp f g).hom.app L.val ≫
      (Modules.pullbackComp f g).inv.app L.val ≫
        (Modules.pullback f).map e.inv ≫ (pullbackUnitIso f).hom = _
    rw [Iso.hom_inv_id_app_assoc]
    apply (cancel_epi ((restrictFunctorIsoPullback f).hom.app
      ((Modules.pullback g).obj L.val))).mp
    rw [← reassoc_of% ((restrictFunctorIsoPullback f).hom.naturality e.inv),
      hur]
    exact he
  have hc := congrArg Iso.hom (dualBoundaryTrivialization_comp f g L e)
  change (dualBoundaryTrivialization (f ≫ g) L e').hom = _ at hc
  rw [he'] at hc
  rw [hc]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv,
    Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% ((restrictFunctorIsoPullback f).hom.naturality
    (dualBoundaryTrivialization g L e).hom), hur]

end AlgebraicGeometry.Scheme.Hom
