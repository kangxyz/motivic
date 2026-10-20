/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeGeometry
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.CurveGeometry

/-!
# Openness of the original native retained-product inclusion

Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeRetainedProduct`.

For a commutative ring R, an affine coefficient open V and any original open
map a to the affine line, the literal original retained-product inclusion is
open. Its retained map is targetNativeRetained R V (a ≫ chart R 0), not a smaller
native parameter open. This specializes the existing Cartesian openness API
and introduces no new object, geometric choice or desired-open premise.

This independently selectable geometric helper retains the literal native
coefficient maps and supplied neighborhoods. Its direct importer is
`RelativeCurve.Pencils.Correction.OriginalTargetSectionWitnesses`; the original
localization history applies the stated openness property to its stored target
retained map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme Scheme.Hom Scheme.RelativeCurvePencil

universe u

namespace AlgebraicGeometry.RelativeProjectiveLine

/-- The original affine-line open stays open on the literal retained product. -/
theorem targetNativeRetainedProduct_chart_open
    (R : Type u) [CommRing R]
    (V : (Spec (.of R)).Opens) [IsAffine V.toScheme]
    {A : Scheme.{u}} (a : A ⟶ Spec (.of (Polynomial R))) [IsOpenImmersion a] :
    IsOpenImmersion
      (retainedProductInclusion
        (chart Γ(V.toScheme, ⊤) 0 ≫
          ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2)))
        (ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2)))
        (targetNativeRetained R V (a ≫ chart R 0))) := by
  let B := Γ(V.toScheme, ⊤)
  let : IsOpenImmersion (a ≫ chart R 0) :=
    MorphismProperty.comp_mem @IsOpenImmersion a (chart R 0)
      (inferInstance : IsOpenImmersion a) (chart_isOpenImmersion R 0)
  have hRetained := targetNativeRetained_open R V (a ≫ chart R 0)
  exact MorphismProperty.of_isPullback
    (retainedProductInclusion_isPullback
      (chart B 0 ≫ ProjectiveSpace.toSpec B (ULift.{u} (Fin 2)))
      (ProjectiveSpace.toSpec B (ULift.{u} (Fin 2)))
      (targetNativeRetained R V (a ≫ chart R 0)))
    hRetained

end AlgebraicGeometry.RelativeProjectiveLine
