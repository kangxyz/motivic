/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairNormIdeal
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.GraphRegular

/-! # Regularity and uniqueness of the original section-pair norm unit

The two additions are extracted from the recovered source without changing
its hypotheses or original coefficient maps. No existing consumer calls either
addition.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairNormUnit`.

The exact hypotheses are the section variables and declaration signatures below.
This is a standalone API with no current direct import consumer.
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
include hl in
/-- The actual transported target coefficient is regular on the open chart.
This uses flatness of the ambient open, not pullback along a closed boundary. -/
theorem sectionPairTargetFrameOnChart_scalar_regular [IsOpenImmersion w] :
    IsSMulRegular Γ(W, ⊤)
      ((l ≫ pullback.snd (Hom.retainedParameterProductMap π f jB jA p hret) vA).appTop
        (Modules.Hom.app (sectionPairGraphCoefficient π jA LA aA bA vA) ⊤
          (1 : Γ(V, ⊤)))) := by
  let i := Hom.targetCompactificationGraph π f jB
  have : Mono (Hom.idealInclusion i) := Hom.idealInclusionMono i
  have : Mono ((Modules.pullback w).map (Hom.idealInclusion i)) :=
    mono_pullback_of_flat_all w (Hom.idealInclusion i)
  have : Mono (pullbackUnitMap w (Hom.idealInclusion i)) := by
    unfold pullbackUnitMap
    infer_instance
  let E := sectionPairTargetFrameOnChart π f jB jA p hret LA aA bA vA w l hl
  have : Mono (E.inv ≫ pullbackUnitMap w (Hom.idealInclusion i)) := mono_comp _ _
  have hr := Modules.isSMulRegular_unitEnd_app_one
    (E.inv ≫ pullbackUnitMap w (Hom.idealInclusion i))
  change IsSMulRegular Γ(W, ⊤) (show Γ(W, ⊤) from Modules.Hom.app
    ((sectionPairTargetFrameOnChart π f jB jA p hret LA aA bA vA w l hl).inv ≫
      pullbackUnitMap w (Hom.idealInclusion (Hom.targetCompactificationGraph π f jB)))
    ⊤ (1 : Γ(W, ⊤))) at hr
  rw [sectionPairTargetFrameOnChart_coordinate,
    Hom.unitEndomorphismPullback_app_one] at hr
  exact hr

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
/-- The actual original graph comparison has one uniquely determined unit. -/
theorem sectionPairGraph_norm_association_unique [IsDomain Γ(W, ⊤)] :
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
      ∃! u : Γ(W, ⊤)ˣ, Algebra.norm Γ(W, ⊤) cB = (u : Γ(W, ⊤)) * cA := by
  dsimp only
  intro hfree
  let : Algebra Γ(W, ⊤) Γ(pullback (Hom.graphProductMap π f jB) w, ⊤) :=
    (pullback.snd (Hom.graphProductMap π f jB) w).appTop.hom.toAlgebra
  let := hfree
  obtain ⟨u, hu⟩ := sectionPairGraph_norm_association
    π f jB jA p hret LA aA bA vA w l hl LB aB bB
  refine ⟨u, hu, ?_⟩
  intro v hv
  apply Units.ext
  apply sectionPairTargetFrameOnChart_scalar_regular π f jB jA p hret LA aA bA vA w l hl
  change _ * (v : Γ(W, ⊤)) = _ * (u : Γ(W, ⊤))
  simpa only [mul_comm] using hv.symm.trans hu

end AlgebraicGeometry.Scheme.RelativeCurvePencil
