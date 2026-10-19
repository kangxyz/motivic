/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.ProjectiveMap.AffineSourceLocalizedFreeCharts
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.ProjectiveMap.AffineSourceFreeCharts
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.Compactification
public import Mathlib.AlgebraicGeometry.AffineScheme
/-! # The original localized free charts on the final common coefficient open

The maps into the original localization are constructed from the retained
inclusion O ≤ D(r), not supplied as independent factorization premises.
The second restriction is exactly the open chosen before the common sections.

Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.CoefficientFreeCharts`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Pencils.NativeSectionPairTransferAction`.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom Scheme.ConstantCurve RelativeProjectiveLine
open AlgebraicGeometry.FiniteSchemeNormBaseChange
universe u
namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

variable (R : Type u) [CommRing R] (r : R)
  (O : (Spec (.of R)).Opens) (hOr : O ≤ PrimeSpectrum.basicOpen r)

/-- The actual first coefficient open maps to the original localization. -/
def originalCoefficientLocalizationMap : O.toScheme ⟶ Spec (.of (Localization.Away r)) :=
  (Spec (.of R)).homOfLE hOr ≫ (basicOpenIsoSpecAway (R := .of R) r).hom

@[reassoc]
theorem originalCoefficientLocalizationMap_spec :
    originalCoefficientLocalizationMap R r O hOr ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) = O.ι := by
  rw [originalCoefficientLocalizationMap, Category.assoc, basicOpenIsoSpecAway_hom_SpecMap,
    Scheme.homOfLE_ι]

variable [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]

/-- The final coefficient open has the same explicit factor through D(r). -/
def finalCoefficientLocalizationMap : V.toScheme ⟶ Spec (.of (Localization.Away r)) :=
  V.ι ≫ O.toScheme.isoSpec.inv ≫ originalCoefficientLocalizationMap R r O hOr

omit [IsAffine V.toScheme] in
@[reassoc]
theorem finalCoefficientLocalizationMap_spec :
    finalCoefficientLocalizationMap R r O hOr V ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) =
      V.ι ≫ O.toScheme.isoSpec.inv ≫ O.ι := by
  simp only [finalCoefficientLocalizationMap, Category.assoc,
    originalCoefficientLocalizationMap_spec]

variable {C : Scheme.{u}}
  (f : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsFinite f]
  (hfree : ∀ i : ULift.{u} (Fin 2),
    let w := chart (Localization.Away r) i ≫
      ProjectiveSpace.map (algebraMap R (Localization.Away r)) (ULift.{u} (Fin 2))
    let : Algebra (Polynomial (Localization.Away r)) Γ(pullback f w, ⊤) :=
      (scalarMap (pullback.snd f w)).toAlgebra
    Module.Free (Polynomial (Localization.Away r)) Γ(pullback f w, ⊤))

include hOr hfree in
/-- The first actual normalized map retains both complete original free charts. -/
theorem originalCoefficient_chart_sections_free (i : ULift.{u} (Fin 2)) :
    let F := boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) f O
    let w := chart Γ(O.toScheme, ⊤) i
    let : Algebra (Polynomial Γ(O.toScheme, ⊤)) Γ(pullback F w, ⊤) :=
      (scalarMap (pullback.snd F w)).toAlgebra
    Module.Free (Polynomial Γ(O.toScheme, ⊤)) Γ(pullback F w, ⊤) := by
  exact affineSourceToProjectiveSpace_chart_sections_free_of_factor R
    (Localization.Away r) (algebraMap R (Localization.Away r)) f O.ι
    (originalCoefficientLocalizationMap R r O hOr)
    (originalCoefficientLocalizationMap_spec R r O hOr).symm hfree i

include hOr hfree in
/-- The final, unchanged common-section map retains both whole free charts.
No new localization or choice of sections is made. -/
theorem finalCoefficient_chart_sections_free (i : ULift.{u} (Fin 2)) :
    let F := boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) f O
    let F' := boundaryBaseProjectiveMap Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)) F V
    let w := chart Γ(V.toScheme, ⊤) i
    let : Algebra (Polynomial Γ(V.toScheme, ⊤)) Γ(pullback F' w, ⊤) :=
      (scalarMap (pullback.snd F' w)).toAlgebra
    Module.Free (Polynomial Γ(V.toScheme, ⊤)) Γ(pullback F' w, ⊤) := by
  exact affineSourceToProjectiveSpace_chart_sections_free Γ(O.toScheme, ⊤)
    (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) f O) V.ι
    (originalCoefficient_chart_sections_free R r O hOr f hfree) i

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
