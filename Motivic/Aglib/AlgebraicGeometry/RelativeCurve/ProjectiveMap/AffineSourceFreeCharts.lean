/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Flat.FreeCartesian
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.ProjectiveMap.AffineSource
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.BaseChange

/-!
# Keep original free projective charts after an actual affine base refinement

The original finite projective map is transported by the native affine-source
base-change construction. Standard-chart compatibility and the actual Cartesian
square preserve coordinate freeness. No new coefficient or frames are selected.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.ProjectiveMap.AffineSourceFreeCharts`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteSchemeNormBaseChange

universe u
namespace AlgebraicGeometry.Scheme.ConstantCurve

/-- Both original standard-chart free modules survive every actual affine base
change, including a further common coefficient open chosen for boundary frames.
The resulting map is the original `affineSourceToProjectiveSpace`, and all
scalar actions come from its literal chart projections. -/
theorem affineSourceToProjectiveSpace_chart_sections_free
    (R : Type u) [CommRing R] {C T : Scheme.{u}} [IsAffine T]
    (f : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsFinite f]
    (b : T ⟶ Spec (.of R))
    (hfree : ∀ i : ULift.{u} (Fin 2),
      let : Algebra (Polynomial R) Γ(Limits.pullback f (RelativeProjectiveLine.chart R i), ⊤) :=
        (scalarMap (pullback.snd f (RelativeProjectiveLine.chart R i))).toAlgebra
      Module.Free (Polynomial R) Γ(Limits.pullback f (RelativeProjectiveLine.chart R i), ⊤))
    (i : ULift.{u} (Fin 2)) :
    let f' := affineSourceToProjectiveSpace R (ULift.{u} (Fin 2)) b f
    let w := RelativeProjectiveLine.chart Γ(T, ⊤) i
    let : Algebra (Polynomial Γ(T, ⊤)) Γ(Limits.pullback f' w, ⊤) :=
      (scalarMap (pullback.snd f' w)).toAlgebra
    Module.Free (Polynomial Γ(T, ⊤)) Γ(Limits.pullback f' w, ⊤) := by
  let f' := affineSourceToProjectiveSpace R (ULift.{u} (Fin 2)) b f
  let w := RelativeProjectiveLine.chart Γ(T, ⊤) i
  have H := (IsPullback.of_hasPullback f' w).paste_horiz
    (affineSourceToProjectiveSpace_isPullback R (ULift.{u} (Fin 2)) b f)
  rw [show w ≫ ProjectiveSpace.map (affineSourceCoefficientMap R b) (ULift.{u} (Fin 2)) =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (affineSourceCoefficientMap R b))) ≫
        RelativeProjectiveLine.chart R i from RelativeProjectiveLine.chart_map _ i] at H
  have Hchart := H.of_right'
    (IsPullback.of_hasPullback f (RelativeProjectiveLine.chart R i))
  let : IsAffine (Limits.pullback f (RelativeProjectiveLine.chart R i)) :=
    isAffine_of_isAffineHom (pullback.snd f (RelativeProjectiveLine.chart R i))
  let : Algebra (Polynomial R) Γ(Limits.pullback f (RelativeProjectiveLine.chart R i), ⊤) :=
    (scalarMap (pullback.snd f (RelativeProjectiveLine.chart R i))).toAlgebra
  let : Module.Free (Polynomial R)
      Γ(Limits.pullback f (RelativeProjectiveLine.chart R i), ⊤) := hfree i
  exact sections_free_of_isPullback (pullback.snd f (RelativeProjectiveLine.chart R i))
    (pullback.snd f' w) _ _ Hchart

end AlgebraicGeometry.Scheme.ConstantCurve
