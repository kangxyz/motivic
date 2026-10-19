/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Flat.FreeCartesian
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.ProjectiveMap.AffineSource
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.BaseChange
/-! # Preserve the original localized free charts through affine refinement

The initial two free modules may belong to a coefficient localization rather
than the original coefficient ring. An actual factorization of the affine
base map preserves them on the literal final native projective charts.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.ProjectiveMap.AffineSourceLocalizedFreeCharts`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`RelativeAffineLine.CoefficientFreeCharts`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteSchemeNormBaseChange

universe u
namespace AlgebraicGeometry.Scheme.ConstantCurve

/-- The coefficient map of the unchanged affine base map respects its actual
factorization through an intermediate affine coefficient scheme. -/
theorem affineSourceCoefficientMap_of_factor
    (R A : Type u) [CommRing R] [CommRing A] (ρ : R →+* A)
    {T : Scheme.{u}} [IsAffine T] (b : T ⟶ Spec (.of R))
    (t : T ⟶ Spec (.of A)) (hb : b = t ≫ Spec.map (CommRingCat.ofHom ρ)) :
    affineSourceCoefficientMap R b = (affineSourceCoefficientMap A t).comp ρ := by
  simp only [affineSourceCoefficientMap, coefficientMap, hb, ← Category.assoc,
    Spec.preimage_comp, Spec.preimage_map, CommRingCat.hom_comp, CommRingCat.hom_ofHom]

/-- Both original coefficient-localized free chart modules survive every
actual affine refinement factoring through that coefficient scheme. In the
localization case, take `A = Localization.Away r` and `ρ = algebraMap R A`.
No new localization, chart, basis or scalar action is selected. -/
theorem affineSourceToProjectiveSpace_chart_sections_free_of_factor
    (R A : Type u) [CommRing R] [CommRing A] (ρ : R →+* A)
    {C T : Scheme.{u}} [IsAffine T]
    (f : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsFinite f]
    (b : T ⟶ Spec (.of R)) (t : T ⟶ Spec (.of A))
    (hb : b = t ≫ Spec.map (CommRingCat.ofHom ρ))
    (hfree : ∀ i : ULift.{u} (Fin 2),
      let w := RelativeProjectiveLine.chart A i ≫
        ProjectiveSpace.map ρ (ULift.{u} (Fin 2))
      let : Algebra (Polynomial A) Γ(Limits.pullback f w, ⊤) :=
        (scalarMap (pullback.snd f w)).toAlgebra
      Module.Free (Polynomial A) Γ(Limits.pullback f w, ⊤))
    (i : ULift.{u} (Fin 2)) :
    let f' := affineSourceToProjectiveSpace R (ULift.{u} (Fin 2)) b f
    let w := RelativeProjectiveLine.chart Γ(T, ⊤) i
    let : Algebra (Polynomial Γ(T, ⊤)) Γ(Limits.pullback f' w, ⊤) :=
      (scalarMap (pullback.snd f' w)).toAlgebra
    Module.Free (Polynomial Γ(T, ⊤)) Γ(Limits.pullback f' w, ⊤) := by
  let f' := affineSourceToProjectiveSpace R (ULift.{u} (Fin 2)) b f
  let w := RelativeProjectiveLine.chart Γ(T, ⊤) i
  let w₀ := RelativeProjectiveLine.chart A i ≫
    ProjectiveSpace.map ρ (ULift.{u} (Fin 2))
  have hw : w ≫ ProjectiveSpace.map (affineSourceCoefficientMap R b)
      (ULift.{u} (Fin 2)) =
      Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (affineSourceCoefficientMap A t))) ≫ w₀ := by
    dsimp only [w, w₀]
    rw [affineSourceCoefficientMap_of_factor R A ρ b t hb, ProjectiveSpace.map_comp,
      ← Category.assoc, RelativeProjectiveLine.chart_map, Category.assoc]
  have H := (IsPullback.of_hasPullback f' w).paste_horiz
    (affineSourceToProjectiveSpace_isPullback R (ULift.{u} (Fin 2)) b f)
  rw [hw] at H
  have Hchart := H.of_right' (IsPullback.of_hasPullback f w₀)
  let : IsAffine (Limits.pullback f w₀) :=
    isAffine_of_isAffineHom (pullback.snd f w₀)
  let : Algebra (Polynomial A) Γ(Limits.pullback f w₀, ⊤) :=
    (scalarMap (pullback.snd f w₀)).toAlgebra
  let : Module.Free (Polynomial A) Γ(Limits.pullback f w₀, ⊤) := hfree i
  exact sections_free_of_isPullback (pullback.snd f w₀)
    (pullback.snd f' w) _ _ Hchart

end AlgebraicGeometry.Scheme.ConstantCurve
