/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLineRatio
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberChartNorm
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.Neighborhood.General

/-!
# The original generic line ratio on its actual affine chart

The canonical generic-fiber chart comparison transports the two original
line-bundle maps together. Their ratio is unchanged, with no supplied
comparison of rational functions and no source function field.


Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberChartLineRatio`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.GenericRatioChartCycle`,
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberChartFrameNorm`,
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLocalRatio`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u
namespace AlgebraicGeometry.Scheme

open Modules Modules.Invertible

variable {C T : Scheme.{u}} [IsIntegral T] (f : C ⟶ T) [IsFinite f]
  (U : T.Opens) (hU : IsAffineOpen U) [Nonempty U]

omit [IsFinite f] in
/-- The actual generic chart projection retains the original source map. -/
@[reassoc (attr := simp)]
theorem genericFiberChartProjection_fst :
    genericFiberChartProjection f U hU ≫ pullback.fst f hU.fromSpec =
      pullback.fst f (T.fromSpecStalk (genericPoint T)) := by
  dsimp only [genericFiberChartProjection]
  rw [Category.assoc, ← genericFiberChartIso_hom_fst, Iso.inv_hom_id_assoc]

omit [IsFinite f] in
/-- Both pullbacks of an original line map differ only by the canonical
composition and equal-base-map isomorphisms. -/
theorem genericFiberChartLineMap_eq (L : LineBundle C)
    (φ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) :
    pullbackUnitMap (genericFiberChartProjection f U hU)
        (pullbackUnitMap (pullback.fst f hU.fromSpec) φ) =
      ((Modules.pullbackComp (genericFiberChartProjection f U hU)
        (pullback.fst f hU.fromSpec)).app L.val).hom ≫
      ((Modules.pullbackCongr (genericFiberChartProjection_fst f U hU)).app L.val).hom ≫
        genericFiberLineMap f L φ := by
  change _ = _ ≫ _ ≫ pullbackUnitMap _ φ
  rw [pullbackUnitMap_congr, pullbackUnitMap_comp]

/-- The nested pullback of an original regular map is invertible, without
requiring a chosen chart frame. -/
instance genericFiberChartLineMap_isIso (L : LineBundle C)
    (ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono ψ] :
    IsIso (pullbackUnitMap (genericFiberChartProjection f U hU)
      (pullbackUnitMap (pullback.fst f hU.fromSpec) ψ)) := by
  rw [genericFiberChartLineMap_eq f U hU L ψ]
  let := genericFiberLineMap_isIso f L ψ
  infer_instance

/-- The global canonical ratio multiplies the original pulled chart
denominator map to its original pulled numerator map. -/
theorem genericFiberChartLineMap_comp_ratio (L : LineBundle C)
    (φ ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] [Mono ψ] :
    pullbackUnitMap (genericFiberChartProjection f U hU)
        (pullbackUnitMap (pullback.fst f hU.fromSpec) ψ) ≫
        (genericFiberLineRatioIso f L φ ψ).hom =
      pullbackUnitMap (genericFiberChartProjection f U hU)
        (pullbackUnitMap (pullback.fst f hU.fromSpec) φ) := by
  rw [genericFiberChartLineMap_eq f U hU L ψ,
    genericFiberChartLineMap_eq f U hU L φ]
  simp only [genericFiberLineRatioIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    asIso_hom, Category.assoc, IsIso.hom_inv_id_assoc]

/-- Computing the ratio on the actual affine chart gives exactly the
original global generic-fiber ratio. -/
theorem genericFiberChartLineRatio_eq (L : LineBundle C)
    (φ ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] [Mono ψ] :
    inv (pullbackUnitMap (genericFiberChartProjection f U hU)
        (pullbackUnitMap (pullback.fst f hU.fromSpec) ψ)) ≫
      pullbackUnitMap (genericFiberChartProjection f U hU)
        (pullbackUnitMap (pullback.fst f hU.fromSpec) φ) =
      (genericFiberLineRatioIso f L φ ψ).hom := by
  apply (cancel_epi (pullbackUnitMap (genericFiberChartProjection f U hU)
    (pullbackUnitMap (pullback.fst f hU.fromSpec) ψ))).mp
  rw [IsIso.hom_inv_id_assoc, genericFiberChartLineMap_comp_ratio]

omit U hU [Nonempty U] in
/-- The canonical ratio norm is nonzero because it is the norm of an actual unit. -/
theorem genericFiberLineRatioNorm_ne_zero (L : LineBundle C)
    (φ ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] [Mono ψ] :
    genericFiberLineRatioNorm f L φ ψ ≠ 0 := by
  let q := pullback.snd f (T.fromSpecStalk (genericPoint T))
  let : IsFinite q := by dsimp [q]; infer_instance
  let : Algebra T.functionField Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap q).toAlgebra
  let : Module.Finite T.functionField
      Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤) :=
    FiniteSchemeNormBaseChange.sections_finite q
  exact ((genericFiberLineRatioUnit f L φ ψ).isUnit.map
    (Algebra.norm T.functionField)).ne_zero

end AlgebraicGeometry.Scheme
