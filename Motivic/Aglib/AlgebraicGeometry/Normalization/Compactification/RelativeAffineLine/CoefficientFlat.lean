/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.CoefficientFreeCharts
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.FlatOfFreeCharts

/-!
# Flatness on the same original and final coefficient opens

The same free-chart witnesses give flatness of the literal first and final
projective coordinate maps. No coefficient, normalization, boundary, or section
is chosen again. These conclusions concern flatness, not fiber dimension or a
complete standard-triple structure.

Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.CoefficientFlat`.
Standalone API; no current external import consumer.
The interfaces and exact hypotheses are given in the declarations below.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom RelativeProjectiveLine
open AlgebraicGeometry.FiniteSchemeNormBaseChange

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

universe u

variable (R : Type u) [CommRing R] (r : R)
  (O : (Spec (.of R)).Opens) (hOr : O ≤ PrimeSpectrum.basicOpen r)
  [IsAffine O.toScheme]
  {C : Scheme.{u}}
  (f : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsFinite f]
  (hfree : ∀ i : ULift.{u} (Fin 2),
    let w := chart (Localization.Away r) i ≫
      ProjectiveSpace.map (algebraMap R (Localization.Away r)) (ULift.{u} (Fin 2))
    let : Algebra (Polynomial (Localization.Away r)) Γ(pullback f w, ⊤) :=
      (scalarMap (pullback.snd f w)).toAlgebra
    Module.Free (Polynomial (Localization.Away r)) Γ(pullback f w, ⊤))

include hOr hfree in
/-- The actual first coefficient map is flat for the original free-chart
witnesses, without a new coefficient choice. -/
theorem originalCoefficient_projectiveMap_flat :
    Flat (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) f O) := by
  exact RelativeProjectiveLine.flat_of_free_chart_sections Γ(O.toScheme, ⊤)
    (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) f O)
    (originalCoefficient_chart_sections_free R r O hOr f hfree)

include hOr hfree in
/-- The final literal coefficient map is flat for the same original free-chart
witnesses and the already selected final open. -/
theorem finalCoefficient_projectiveMap_flat
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme] :
    let F := boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) f O
    Flat (boundaryBaseProjectiveMap Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)) F V) := by
  exact RelativeProjectiveLine.flat_of_free_chart_sections Γ(V.toScheme, ⊤)
    (boundaryBaseProjectiveMap Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2))
      (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) f O) V)
    (finalCoefficient_chart_sections_free R r O hOr V f hfree)

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
