/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairGraphCoordinate
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberFunctionalRatio
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLineRatioInverse
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.FunctionalQuotientAffineChart
/-! # The original target coefficient and its parameter-pulled generic ratio

Only the identity of the actual parameter product is normed. The parameter map
itself is not assumed finite and is never assigned a determinant norm. Literal
pulled functionals and their composition comparisons are retained.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.SectionPairTargetGenericRatio`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Norm.SectionPairNormNeighborhood`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- The inverse identity norm of the same original target ratio is the germ of
its actual affine graph coefficient after the actual parameter map. -/
theorem sectionPairTarget_genericRatio_inv_eq_chart_germ
    {S C Y T : Scheme.{u}} (π : C ⟶ S) [IsSeparated π]
    (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
    (L : LineBundle (pullback (j ≫ π) π))
    (a : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
      (tensorLineBundle _ L (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))).val)
    (b : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ L.val)
    [IsIntegral T] (κ : T ⟶ pullback (j ≫ π) π)
    (U : T.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [IsIso (Hom.pullbackToUnit (sectionDualFunctional _
      (tensorLineBundle _ L (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))) a)
        (U.ι ≫ κ))]
    [IsIso (Hom.pullbackToUnit (sectionDualFunctional _
      (tensorLineBundle _ L (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))) a)
        (hU.fromSpec ≫ κ))]
    [IsIso (Hom.pullbackToUnit (sectionDualFunctional _ L b) (hU.fromSpec ≫ κ))] :
    let M := tensorLineBundle _ L (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))
    let c := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) L
      (Hom.idealInclusion (Hom.compactificationGraph π j)) b
    let af := sectionDualFunctional _ M a
    let cf := sectionDualFunctional _ M c
    let Mκ := pullbackLineBundle κ (dualLineBundle _ M)
    ∀ [Mono (pullbackUnitMap κ af)] [Mono (pullbackUnitMap κ cf)],
      (genericFiberLineRatioNorm (𝟙 T) Mκ
        (pullbackUnitMap κ af) (pullbackUnitMap κ cf))⁻¹ =
      T.germToFunctionField U ((Scheme.ΓSpecIso Γ(T, U)).hom
        (Modules.Hom.app (sectionPairGraphCoefficient π j L a b (hU.fromSpec ≫ κ)) ⊤
          (1 : Γ(Spec Γ(T, U), ⊤)))) := by
  dsimp only
  intro haf hcf
  let M := tensorLineBundle _ L (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))
  let c := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) L
    (Hom.idealInclusion (Hom.compactificationGraph π j)) b
  let af := sectionDualFunctional _ M a
  let cf := sectionDualFunctional _ M c
  let Mκ := pullbackLineBundle κ (dualLineBundle _ M)
  let : Mono (pullbackUnitMap κ af) := haf
  let : Mono (pullbackUnitMap κ cf) := hcf
  let : IsIso (pullbackUnitMap (U.ι ≫ κ) af) := by
    change IsIso (Hom.pullbackToUnit af (U.ι ≫ κ))
    dsimp only [af, M]
    infer_instance
  let : IsIso (pullbackUnitMap (hU.fromSpec ≫ κ) af) := by
    change IsIso (Hom.pullbackToUnit af (hU.fromSpec ≫ κ))
    dsimp only [af, M]
    infer_instance
  let := pullbackUnitMap_nested_isIso_of_comp κ U.ι af
  have hn := genericFiberLineRatioNorm_id_eq_functionalQuotient_germ Mκ
    (pullbackUnitMap κ cf) (pullbackUnitMap κ af) U
  rw [genericFiberLineRatioNorm_swap] at hn
  have hc := functionalQuotient_parameter_fromSpec_coefficient κ cf af U hU
  have hθ : sectionPairGraphCoefficient π j L a b (hU.fromSpec ≫ κ) =
      inv (pullbackUnitMap (hU.fromSpec ≫ κ) af) ≫
        pullbackUnitMap (hU.fromSpec ≫ κ) cf :=
    sectionPairIdealFrame_graphCoefficient (hU.fromSpec ≫ κ)
      (Hom.relativeCompactificationGraphLine π j) L b a
      (Hom.idealInclusion (Hom.compactificationGraph π j))
  rw [hθ, hc]
  exact hn

end AlgebraicGeometry.Scheme.RelativeCurvePencil
