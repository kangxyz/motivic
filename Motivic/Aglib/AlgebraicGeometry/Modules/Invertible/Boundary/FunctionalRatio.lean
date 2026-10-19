/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.PairedScalar
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateUnitOnOpen

/-! # Original boundary equations for local functional quotients

Only the local denominator functional is inverted. On an arbitrary boundary,
including a nonreduced one, the original section equation determines its scalar.
No inverse of the section on the enlarged chart is assumed.


Intended upstream module: `Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.FunctionalRatio`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.NormalizedTwistedIdealCoordinate`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.FunctionalGraphRatioBoundary`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.FunctionalRatioBoundary`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- An original scalar equation between pulled sections gives the same scalar
in the literal pulled dual-functional equation. -/
theorem pullback_sectionScalar_dualFunctional {X W : Scheme.{u}} (f : W ⟶ X)
    (L : LineBundle X) (n d : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    (θ : SheafOfModules.unit W.ringCatSheaf ⟶ SheafOfModules.unit W.ringCatSheaf)
    (h : pullbackSectionMap f n = θ ≫ pullbackSectionMap f d) :
    pullbackUnitMap f (sectionDualFunctional X L d) ≫ θ =
      pullbackUnitMap f (sectionDualFunctional X L n) := by
  change Hom.pullbackToUnit (sectionDualFunctional X L d) f ≫ θ =
    Hom.pullbackToUnit (sectionDualFunctional X L n) f
  rw [sectionDualFunctional_pullback, sectionDualFunctional_pullback]
  let P := (PullbackTensor.Local.pullbackLineBundleTensorIso f (dualLineBundle X L) L).inv ≫
    (Modules.pullback f).map (dualEvaluationIso X L).hom ≫ (pullbackUnitIso f).hom
  change pairedSectionFunctional W P (pullbackSectionMap f d) ≫ θ =
    pairedSectionFunctional W P (pullbackSectionMap f n)
  rw [h, pairedSectionFunctional_unitEnd]

/-- The original boundary functional equation determines the restriction of
its actual local quotient. Cancellation uses only the denominator's genuine unit chart. -/
theorem functionalQuotient_boundary_of_equation
    {X W B : Scheme.{u}} (w : W ⟶ X) (r : B ⟶ W) {M : X.Modules}
    (φ ψ : M ⟶ SheafOfModules.unit X.ringCatSheaf) [IsIso (pullbackUnitMap w ψ)]
    (θ : SheafOfModules.unit B.ringCatSheaf ⟶ SheafOfModules.unit B.ringCatSheaf)
    (h : pullbackUnitMap (r ≫ w) ψ ≫ θ = pullbackUnitMap (r ≫ w) φ) :
    Hom.unitEndomorphismPullback r (inv (pullbackUnitMap w ψ) ≫ pullbackUnitMap w φ) = θ := by
  let ρ := inv (pullbackUnitMap w ψ) ≫ pullbackUnitMap w φ
  have hρ : pullbackUnitMap w ψ ≫ ρ = pullbackUnitMap w φ := by
    simp only [ρ, IsIso.hom_inv_id_assoc]
  have hp : pullbackUnitMap r (pullbackUnitMap w ψ) ≫
      Hom.unitEndomorphismPullback r ρ = pullbackUnitMap r (pullbackUnitMap w φ) := by
    have hh := congrArg (pullbackUnitMap r) hρ
    simpa only [pullbackUnitMap, Hom.unitEndomorphismPullback, Functor.map_comp,
      Category.assoc, Iso.hom_inv_id_assoc] using hh
  have hθ : pullbackUnitMap r (pullbackUnitMap w ψ) ≫ θ =
      pullbackUnitMap r (pullbackUnitMap w φ) := by
    rw [← pullbackUnitMap_comp, ← pullbackUnitMap_comp, Category.assoc, h]
  have : IsIso (pullbackUnitMap r (pullbackUnitMap w ψ)) := by
    change IsIso ((Modules.pullback r).map (pullbackUnitMap w ψ) ≫ (pullbackUnitIso r).hom)
    infer_instance
  exact (cancel_epi (pullbackUnitMap r (pullbackUnitMap w ψ))).mp (hp.trans hθ.symm)

/-- The SAME section boundary equation computes the original local functional
ratio, without requiring a section-unit proof on the enlarged chart. -/
theorem functionalQuotient_boundary_of_sectionEquation
    {X W B : Scheme.{u}} (w : W ⟶ X) (r : B ⟶ W) (L : LineBundle X)
    (n d : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    [IsIso (pullbackUnitMap w (sectionDualFunctional X L d))]
    (θ : SheafOfModules.unit B.ringCatSheaf ⟶ SheafOfModules.unit B.ringCatSheaf)
    (h : pullbackSectionMap (r ≫ w) n = θ ≫ pullbackSectionMap (r ≫ w) d) :
    Hom.unitEndomorphismPullback r
      (inv (pullbackUnitMap w (sectionDualFunctional X L d)) ≫
        pullbackUnitMap w (sectionDualFunctional X L n)) = θ :=
  functionalQuotient_boundary_of_equation w r _ _ θ
    (pullback_sectionScalar_dualFunctional (r ≫ w) L n d θ h)

end AlgebraicGeometry.Scheme.Modules.Invertible
