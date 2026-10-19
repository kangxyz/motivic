/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.PrescribedGraphCoordinate
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RetainedTargetChartFrame

/-! # The marked value of the same original target frame

The actual inverse target chart retains the prescribed frame. Its marked
factor is constructed by the original graph-boundary Cartesian square from
the actual marked projection equation, not supplied as a scalar normalization.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.RetainedTargetPrescribedScalar`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.RetainedTargetNativeScalar`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

private theorem retained_chart_scalar
    {S C P X Y W B : Scheme.{u}} (q : P ⟶ S) (f : C ⟶ P)
    (jB : Y ⟶ C) (jA : X ⟶ P) (p : Y ⟶ X) (h : jB ≫ f = p ≫ jA) [Flat p]
    [IsClosedImmersion (compactificationGraph q jA)]
    [IsClosedImmersion (targetCompactificationGraph q f jB)]
    (hI : IsLocallyRankOne _ (idealModule (compactificationGraph q jA)))
    (v : W ⟶ pullback (jA ≫ q) q)
    (e : (Modules.pullback v).obj (idealModule (compactificationGraph q jA)) ≅
      SheafOfModules.unit W.ringCatSheaf)
    (β : B ⟶ pullback (retainedParameterProductMap q f jB jA p h) v) :
    β.appTop (Modules.Hom.app ((retainedTargetChartFrame q f jB jA p h hI v e).inv ≫
      pullbackUnitMap (pullback.fst (retainedParameterProductMap q f jB jA p h) v)
        (idealInclusion (targetCompactificationGraph q f jB))) ⊤
          (1 : Γ(pullback (retainedParameterProductMap q f jB jA p h) v, ⊤))) =
    (β ≫ pullback.snd (retainedParameterProductMap q f jB jA p h) v).appTop
      (Modules.Hom.app (e.inv ≫ pullbackUnitMap v
        (idealInclusion (compactificationGraph q jA))) ⊤ (1 : Γ(W, ⊤))) := by
  rw [retainedTargetChartFrame_coordinate]
  exact congrArg (fun x => β.appTop x)
    (unitEndomorphismPullback_app_one
      (pullback.snd (retainedParameterProductMap q f jB jA p h) v)
      (e.inv ≫ pullbackUnitMap v (idealInclusion (compactificationGraph q jA))))

private theorem ambient_frame_coordinate
    {P B : Scheme.{u}} {A : P.affineOpens} {b : B ⟶ A.val.toScheme}
    {L : LineBundle P}
    {e : (Modules.pullback b).obj (pullbackLineBundle A.val.ι L).val ≅
      SheafOfModules.unit B.ringCatSheaf}
    (E : PrescribedAffineFrameExtension A b L e)
    (φ : L.val ⟶ SheafOfModules.unit P.ringCatSheaf) :
    E.ambientFrame.inv ≫ pullbackUnitMap E.ambientInclusion φ =
      E.frame.inv ≫ pullbackUnitMap E.inclusion (pullbackUnitMap A.val.ι φ) := by
  simp only [PrescribedAffineFrameExtension.ambientFrame, Iso.trans_inv,
    Iso.symm_inv, Category.assoc]
  exact congrArg (fun θ => E.frame.inv ≫ θ)
    (pullbackUnitMap_comp E.inclusion A.val.ι φ)

variable {S X Y Z C D : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (qC : C ⟶ S) [IsSeparated qC]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ qC)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ qC = p ≫ q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (h : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget q z))
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))


variable (A : (pullback (j ≫ qC) qC).affineOpens)
  (b : (pullback (pullback.snd (j ≫ qC) qC) d ⨿ pullback (j ≫ qC) (s ≫ j ≫ qC)) ⟶
    A.val.toScheme)
  (hc : b ≫ A.val.ι =
    coprod.desc (infinityProductMap qC j d) (graphBoundaryRestriction qC j s))
  (E : PrescribedAffineFrameExtension A b (relativeCompactificationGraphLine qC j)
    ((Modules.pullbackComp b A.val.ι).app (relativeCompactificationGraphLine qC j).val ≪≫
      (Modules.pullbackCongr hc).app (relativeCompactificationGraphLine qC j).val ≪≫
      relativeFullBoundaryIdealFrame q qC j p hq z s h H e d hd))


variable {B U : Scheme.{u}} (f : B ⟶ C) (jB : U ⟶ B)
  (η : U ⟶ Y) [Flat η] (hret : jB ≫ f = η ≫ j)
  [IsClosedImmersion (compactificationGraph qC j)]
  {Q : Type u} [CommRing Q]
  (β : Spec (.of Q) ⟶ pullback (retainedParameterProductMap qC f jB j η hret)
    E.ambientInclusion)
  (a : Spec (.of Q) ⟶ Z)
  (hpoint : (β ≫ pullback.snd (retainedParameterProductMap qC f jB j η hret)
      E.ambientInclusion ≫ E.ambientInclusion) ≫ pullback.snd (j ≫ qC) qC =
        a ≫ (s ≫ j))

/-- The actual marked factor of the SAME target inverse chart is built internally. -/
def retainedTargetMarkedFactor : Spec (.of Q) ⟶ pullback (j ≫ qC) (s ≫ j ≫ qC) :=
  (graphBoundaryRestriction_isPullback qC j s).lift
    (β ≫ pullback.snd (retainedParameterProductMap qC f jB j η hret)
      E.ambientInclusion ≫ E.ambientInclusion) a hpoint

/-- The target graph scalar retains the original supplied-e value under ΓSpecIso.
The entire marked scheme is retained; the scalar need not be invertible. -/
theorem retainedTargetChartFrame_marked_value :
    let eT := retainedTargetChartFrame qC f jB j η hret
      (relativeCompactificationGraphLine qC j).property E.ambientInclusion E.ambientFrame
    let θT := eT.inv ≫ pullbackUnitMap
      (pullback.fst (retainedParameterProductMap qC f jB j η hret) E.ambientInclusion)
      (idealInclusion (targetCompactificationGraph qC f jB))
    let r := retainedTargetMarkedFactor q qC j p hq z s h H e d hd A b hc E
      f jB η hret β a hpoint
    (Scheme.ΓSpecIso (.of Q)).hom
      (β.appTop (Modules.Hom.app θT ⊤
        (1 : Γ(pullback (retainedParameterProductMap qC f jB j η hret)
          E.ambientInclusion, ⊤)))) =
    (Scheme.ΓSpecIso (.of Q)).hom (Modules.Hom.app
      (unitEndomorphismPullback
        (r ≫ (relativeBoundaryProductIso q qC j p hq z s h).hom ≫ boundaryProductMap q p z)
        (e.hom ≫ idealInclusion (boundaryGraphTarget q z))) ⊤ (1 : Γ(Spec (.of Q), ⊤))) := by
  dsimp only
  apply congrArg (fun x : Γ(Spec (.of Q), ⊤) => (Scheme.ΓSpecIso (.of Q)).hom x)
  have hh := retained_chart_scalar qC f jB j η hret
    (relativeCompactificationGraphLine qC j).property E.ambientInclusion E.ambientFrame β
  have hθ := ambient_frame_coordinate E (idealInclusion (compactificationGraph qC j))
  have hs := congrArg (fun θ : SheafOfModules.unit E.neighborhood.ringCatSheaf ⟶
      SheafOfModules.unit E.neighborhood.ringCatSheaf =>
    (β ≫ pullback.snd (retainedParameterProductMap qC f jB j η hret)
      E.ambientInclusion).appTop (Modules.Hom.app θ ⊤ (1 : Γ(E.neighborhood, ⊤)))) hθ
  have hm := prescribedGraphFrame_marked_scalar_of_ambient_eq
    q qC j p hq z s h H e d hd A b hc E
    (β ≫ pullback.snd (retainedParameterProductMap qC f jB j η hret) E.ambientInclusion)
    (retainedTargetMarkedFactor q qC j p hq z s h H e d hd A b hc E
      f jB η hret β a hpoint) (by
        exact ((graphBoundaryRestriction_isPullback qC j s).lift_fst _ _ hpoint).symm)
  exact hh.trans (hs.trans hm)

end AlgebraicGeometry.Scheme.Hom
