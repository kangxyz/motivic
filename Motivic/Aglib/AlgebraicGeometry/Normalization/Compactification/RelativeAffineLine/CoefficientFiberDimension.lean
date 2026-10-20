/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Dimension.FiberComponents
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.CoefficientFlat

/-!
# Native fiber component dimension on the same coefficient opens

For the fixed finite projective-line map over a commutative coefficient ring,
the original localized whole-chart freeness witnesses, the original affine
coefficient open, and the already selected final affine coefficient open,
every component of each literal structural fiber has dimension one.
The exact hypotheses, scalar maps, and pullback projections are in the
signatures below. No additional open, normalization, boundary, section,
nonempty-source premise, or positive rank is chosen or assumed.

Intended upstream module: `CoefficientFiberDimension` in
`Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine`.
The current application is the first and final restrictions of the original
relative affine-line normalization, using the same free-chart witnesses as
`CoefficientFlat`. These componentwise conclusions do not assemble a standard triple.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

open Scheme.Hom RelativeProjectiveLine
open AlgebraicGeometry.FiniteSchemeNormBaseChange

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
/-- The first coefficient restriction retains pure one-dimensional native fibers. -/
theorem originalCoefficient_fiber_component_dimension
    (s : O.toScheme)
    {Z : Set ((pullback.fst O.ι
      (f ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))).fiber s)}
    (hZ : Z ∈ irreducibleComponents ((pullback.fst O.ι
      (f ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))).fiber s)) :
    topologicalKrullDim Z = 1 := by
  let : Flat (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) f O) :=
    originalCoefficient_projectiveMap_flat R r O hOr f hfree
  exact RelativeProjectiveLine.topologicalKrullDim_eq_one_of_mem_nativeFiberComponents
    Γ(O.toScheme, ⊤)
    (pullback.fst O.ι (f ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))
    (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) f O)
    O.toScheme.isoSpec
    (boundaryBaseProjectiveMap_toSpec R (ULift.{u} (Fin 2)) f O) s hZ

include hOr hfree in
/-- The final coefficient restriction uses the same original free-chart witnesses. -/
theorem finalCoefficient_fiber_component_dimension
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]
    (s : V.toScheme)
    {Z : Set ((pullback.fst V.ι
      (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) f O ≫
        ProjectiveSpace.toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)))).fiber s)}
    (hZ : Z ∈ irreducibleComponents ((pullback.fst V.ι
      (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) f O ≫
        ProjectiveSpace.toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)))).fiber s)) :
    topologicalKrullDim Z = 1 := by
  let F := boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) f O
  let F' := boundaryBaseProjectiveMap Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)) F V
  let : Flat F' := finalCoefficient_projectiveMap_flat R r O hOr f hfree V
  exact RelativeProjectiveLine.topologicalKrullDim_eq_one_of_mem_nativeFiberComponents
    Γ(V.toScheme, ⊤)
    (pullback.fst V.ι (F ≫
      ProjectiveSpace.toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2))))
    F' V.toScheme.isoSpec
    (boundaryBaseProjectiveMap_toSpec Γ(O.toScheme, ⊤)
      (ULift.{u} (Fin 2)) F V) s hZ

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
