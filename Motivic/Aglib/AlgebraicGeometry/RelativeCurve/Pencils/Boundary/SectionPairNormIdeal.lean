/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.RetainedSectionPairCoefficient
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.FlatChartIdealCoordinate

/-! # The actual norm ideal in the two original section-pair frames

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairNormIdeal`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S C P X Y W V : Scheme.{u}} (π : P ⟶ S) [IsSeparated π]
  (f : C ⟶ P) [IsFinite f] (jB : Y ⟶ C) [IsOpenImmersion jB]
  [SmoothOfRelativeDimension 1 (jB ≫ f ≫ π)]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) [Flat p] (hret : jB ≫ f = p ≫ jA)
  (LA : LineBundle (pullback (jA ≫ π) π))
  (aA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))).val)
  (bA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶ LA.val)
  (vA : V ⟶ pullback (jA ≫ π) π)
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _ LA bA) vA)]
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _
    (tensorLineBundle _ LA (dualLineBundle _
      (Hom.relativeCompactificationGraphLine π jA))) aA) vA)]
  (w : W ⟶ pullback (jB ≫ f ≫ π) π)
  (l : W ⟶ pullback (Hom.retainedParameterProductMap π f jB jA p hret) vA)
  (hl : l ≫ pullback.fst (Hom.retainedParameterProductMap π f jB jA p hret) vA = w)

local instance : IsClosedImmersion (Hom.compactificationGraph π jA) := by
  dsimp [Hom.compactificationGraph]
  infer_instance

omit [IsFinite f] [IsOpenImmersion jB]
  [SmoothOfRelativeDimension 1 (jB ≫ f ≫ π)] in
include hret in
/-- The target graph ideal is the flat pullback of the original native ideal. -/
theorem retainedTargetGraph_locallyRankOne :
    IsLocallyRankOne _ (Hom.idealModule (Hom.targetCompactificationGraph π f jB)) :=
  isLocallyRankOne_of_iso _
    (Hom.retainedParameterGraphIdealIso π f jB jA p hret
      (Hom.relativeCompactificationGraphLine π jA).property)
    (pullback_locallyRankOne _ _ (Hom.relativeCompactificationGraphLine π jA).property)

/-- The fixed target section-pair frame on the selected original chart. -/
def sectionPairTargetFrameOnChart :
    (Modules.pullback w).obj (Hom.idealModule (Hom.targetCompactificationGraph π f jB)) ≅
      SheafOfModules.unit W.ringCatSheaf :=
  ((Modules.pullbackCongr hl).app
    (Hom.idealModule (Hom.targetCompactificationGraph π f jB))).symm ≪≫
  compositeBoundaryFrame l
    (pullback.fst (Hom.retainedParameterProductMap π f jB jA p hret) vA)
    (Hom.idealModule (Hom.targetCompactificationGraph π f jB))
    (Hom.retainedTargetChartFrame π f jB jA p hret
      (Hom.relativeCompactificationGraphLine π jA).property vA
      (sectionPairIdealFrame vA (Hom.relativeCompactificationGraphLine π jA) LA bA aA))

omit [IsFinite f] [IsOpenImmersion jB]
  [SmoothOfRelativeDimension 1 (jB ≫ f ≫ π)] in
/-- Its coordinate is the original target coefficient under the actual chart map. -/
theorem sectionPairTargetFrameOnChart_coordinate :
    (sectionPairTargetFrameOnChart π f jB jA p hret LA aA bA vA w l hl).inv ≫
      pullbackUnitMap w (Hom.idealInclusion (Hom.targetCompactificationGraph π f jB)) =
    Hom.unitEndomorphismPullback
      (l ≫ pullback.snd (Hom.retainedParameterProductMap π f jB jA p hret) vA)
      (sectionPairGraphCoefficient π jA LA aA bA vA) := by
  simp only [sectionPairTargetFrameOnChart, Iso.trans_inv, Iso.symm_inv, Category.assoc]
  rw [pullbackUnitMap_congr, compositeBoundaryFrame_functional_coordinate,
    retainedSectionPairChartFrame_coordinate, ← Hom.unitEndomorphismPullback_comp]

variable [IsAffine W] [IsOpenImmersion w]
  (LB : LineBundle (pullback (jB ≫ f ≫ π) (f ≫ π)))
  (aB : SheafOfModules.unit (pullback (jB ≫ f ≫ π) (f ≫ π)).ringCatSheaf ⟶
    (tensorLineBundle _ LB (dualLineBundle _
      (Hom.relativeCompactificationGraphLine (f ≫ π) jB))).val)
  (bB : SheafOfModules.unit (pullback (jB ≫ f ≫ π) (f ≫ π)).ringCatSheaf ⟶ LB.val)
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _ LB bB)
    (pullback.fst (Hom.graphProductMap π f jB) w))]
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _
    (tensorLineBundle _ LB (dualLineBundle _
      (Hom.relativeCompactificationGraphLine (f ≫ π) jB))) aB)
    (pullback.fst (Hom.graphProductMap π f jB) w))]

include hl in
/-- The literal graph triangle supplies norm-ideal equality for the same two
section-induced coefficients, with only the original total chart module free. -/
theorem sectionPairGraph_norm_span :
    let vB := pullback.fst (Hom.graphProductMap π f jB) w
    let cB : Γ(pullback (Hom.graphProductMap π f jB) w, ⊤) := Modules.Hom.app
      (sectionPairGraphCoefficient (f ≫ π) jB LB aB bB vB) ⊤
      (1 : Γ(pullback (Hom.graphProductMap π f jB) w, ⊤))
    let cA : Γ(W, ⊤) :=
      (l ≫ pullback.snd (Hom.retainedParameterProductMap π f jB jA p hret) vA).appTop
        (Modules.Hom.app (sectionPairGraphCoefficient π jA LA aA bA vA) ⊤ (1 : Γ(V, ⊤)))
    let : Algebra Γ(W, ⊤) Γ(pullback (Hom.graphProductMap π f jB) w, ⊤) :=
      (pullback.snd (Hom.graphProductMap π f jB) w).appTop.hom.toAlgebra
    ∀ [Module.Free Γ(W, ⊤) Γ(pullback (Hom.graphProductMap π f jB) w, ⊤)],
      Ideal.span {Algebra.norm Γ(W, ⊤) cB} = Ideal.span {cA} := by
  dsimp only
  intro hfree
  let : Algebra Γ(W, ⊤) Γ(pullback (Hom.graphProductMap π f jB) w, ⊤) :=
    (pullback.snd (Hom.graphProductMap π f jB) w).appTop.hom.toAlgebra
  let := hfree
  let vB := pullback.fst (Hom.graphProductMap π f jB) w
  let eB := sectionPairIdealFrame vB (Hom.relativeCompactificationGraphLine (f ≫ π) jB)
    LB bB aB
  let eA := sectionPairTargetFrameOnChart π f jB jA p hret LA aA bA vA w l hl
  have hN := Hom.span_norm_originalGraph_chart π f jB w
    (Hom.relativeCompactificationGraphLine (f ≫ π) jB).property
    (retainedTargetGraph_locallyRankOne π f jB jA p hret) eB eA
  rw [Hom.flatChartIdealTopFrame_scalar, Hom.flatChartIdealTopFrame_scalar] at hN
  have hcoord := sectionPairTargetFrameOnChart_coordinate π f jB jA p hret LA aA bA vA w l hl
  have hs := congrArg
    (fun θ : SheafOfModules.unit W.ringCatSheaf ⟶ SheafOfModules.unit W.ringCatSheaf =>
      Modules.Hom.app θ ⊤ (1 : Γ(W, ⊤))) hcoord
  have hs' := hs.trans (Hom.unitEndomorphismPullback_app_one
    (l ≫ pullback.snd (Hom.retainedParameterProductMap π f jB jA p hret) vA)
    (sectionPairGraphCoefficient π jA LA aA bA vA))
  exact hN.trans (congrArg (fun c : Γ(W, ⊤) => Ideal.span ({c} : Set Γ(W, ⊤))) hs')

include hl in
/-- A single association unit for the actual two coefficients. Boundary values
are proved for this same unit, separately on marked and infinity components. -/
theorem sectionPairGraph_norm_association [IsDomain Γ(W, ⊤)] :
    let vB := pullback.fst (Hom.graphProductMap π f jB) w
    let cB : Γ(pullback (Hom.graphProductMap π f jB) w, ⊤) := Modules.Hom.app
      (sectionPairGraphCoefficient (f ≫ π) jB LB aB bB vB) ⊤
      (1 : Γ(pullback (Hom.graphProductMap π f jB) w, ⊤))
    let cA : Γ(W, ⊤) :=
      (l ≫ pullback.snd (Hom.retainedParameterProductMap π f jB jA p hret) vA).appTop
        (Modules.Hom.app (sectionPairGraphCoefficient π jA LA aA bA vA) ⊤ (1 : Γ(V, ⊤)))
    let : Algebra Γ(W, ⊤) Γ(pullback (Hom.graphProductMap π f jB) w, ⊤) :=
      (pullback.snd (Hom.graphProductMap π f jB) w).appTop.hom.toAlgebra
    ∀ [Module.Free Γ(W, ⊤) Γ(pullback (Hom.graphProductMap π f jB) w, ⊤)],
      ∃ u : Γ(W, ⊤)ˣ, Algebra.norm Γ(W, ⊤) cB = (u : Γ(W, ⊤)) * cA := by
  dsimp only
  intro hfree
  let : Algebra Γ(W, ⊤) Γ(pullback (Hom.graphProductMap π f jB) w, ⊤) :=
    (pullback.snd (Hom.graphProductMap π f jB) w).appTop.hom.toAlgebra
  let := hfree
  have hspan := sectionPairGraph_norm_span π f jB jA p hret LA aA bA vA w l hl LB aB bB
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.mp hspan).symm
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
