/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Source.NativeParameter
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.EtaleCurve

/-!
# The literal native source is smooth over the same coefficient base

Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Source.NativeSmooth`.

For a commutative ring R, an affine coefficient open V and any original open
map a to the affine line, the unchanged native restriction followed by chart
zero and the structure map is smooth of relative dimension one. No affine or
nonempty source premise is required.

This reusable geometric helper retains the literal native coefficient maps
and supplied neighborhood. It is independently selectable; the current
sheafification proof obtains its relative smoothness from its stored geometry.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme Scheme.Hom

universe u

namespace AlgebraicGeometry.RelativeProjectiveLine

/-- The literal native restriction of an open affine-line map is a smooth curve. -/
theorem sourceNativeCoverMap_chart_smooth
    (R : Type u) [CommRing R]
    (V : (Spec (.of R)).Opens) [IsAffine V.toScheme]
    {A : Scheme.{u}} (a : A ⟶ Spec (.of (Polynomial R))) [IsOpenImmersion a] :
    SmoothOfRelativeDimension 1
      ((sourceNativeCoverMap R V a ≫ chart Γ(V.toScheme, ⊤) 0) ≫
        ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2))) := by
  let B := Γ(V.toScheme, ⊤)
  have hChart : SmoothOfRelativeDimension 1
      (chart B 0 ≫ ProjectiveSpace.toSpec B (ULift.{u} (Fin 2))) :=
    Eq.mpr
      (congrArg
        (fun f : Spec (.of (Polynomial B)) ⟶ Spec (.of B) =>
          SmoothOfRelativeDimension 1 f)
        (chart_toSpec B (0 : ULift.{u} (Fin 2))))
      (Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one B)
  let := sourceNativeCoverMap_open R V a
  have hZero : SmoothOfRelativeDimension 0 (sourceNativeCoverMap R V a) := inferInstance
  have hComposite := smoothOfRelativeDimension_comp (n := 0) (m := 1)
    (sourceNativeCoverMap R V a)
    (chart B 0 ≫ ProjectiveSpace.toSpec B (ULift.{u} (Fin 2)))
    (hf := hZero) (hg := hChart)
  exact Eq.mpr
    (congrArg
      (fun f : (boundaryBaseCoverOpen (boundaryLineProjection R) a ⊤ V).toScheme ⟶
          Spec (.of B) => SmoothOfRelativeDimension 1 f)
      (Category.assoc (sourceNativeCoverMap R V a) (chart B 0)
        (ProjectiveSpace.toSpec B (ULift.{u} (Fin 2)))))
    hComposite

end AlgebraicGeometry.RelativeProjectiveLine
