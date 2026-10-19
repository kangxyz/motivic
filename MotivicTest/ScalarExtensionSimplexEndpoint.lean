/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SuslinVoevodsky.ScalarExtensionSimplexEndpoint

/-!
# Consumers of literal scalar-extension simplex endpoint charts

Both cofaces use their actual polynomial endpoints, and the whole original
support fiber keeps its source inclusion after the chart comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.FiniteFlatCurve
open AlgebraicGeometry.ScalarExtensionEndpointFiber
open Motivic.ScalarExtensionSimplexEndpoint
open scoped Polynomial Simplicial

universe u

namespace MotivicTest.ScalarExtensionSimplexEndpoint

variable {k E : Type u} [Field k] [Field E] (c : k →+* E)

/-- The actual source scalar map uses the literal polynomial coefficient map. -/
example : sourceScalarMap c 1 ≫ (sourceChart1 k).hom =
    (sourceChart1 E).hom ≫ coefficientMap c := sourceScalarMap_chart1 c

/-- The first product coface cuts out zero in the actual polynomial chart. -/
theorem zeroEndpoint : faceMap k 0 ≫ (sourceChart1 k).hom =
    (sourceChart0 k).hom ≫ endpoint (0 : k) := by
  simpa using faceMap_chart k 0

/-- The second product coface cuts out one in that same chart. -/
theorem oneEndpoint : faceMap k 1 ≫ (sourceChart1 k).hom =
    (sourceChart0 k).hom ≫ endpoint (1 : k) := by
  simpa using faceMap_chart k 1

/-- The comparison keeps an arbitrary original target map after the support inclusion. -/
theorem chartOriginalTarget {C T : Scheme.{u}} (f : C ⟶ (source k 1).left)
    (g : C ⟶ T) (i : Fin 2) :
    (chartFiberIso k f i).hom ≫
        fiberInclusion (f ≫ (sourceChart1 k).hom) (i.val : k) ≫ g =
      pullback.snd (faceMap k i) f ≫ g :=
  chartFiberIso_hom_inclusion_assoc k f i g

open Lean in
run_cmd do
  for name in #[
      ``sourceChart0, ``sourceChart1, ``sourceScalarMap_snd,
      ``oneCoordinateEquiv_symm_coefficients, ``oneSchemeIso_coefficients,
      ``sourceScalarMap_chart1, ``sourceScalarMap_chart0, ``faceMap_chart,
      ``chartFiber_isPullback, ``chartFiberIso, ``chartFiberIso_hom_inclusion,
      ``chartFiberIso_hom_scalar, ``zeroEndpoint, ``oneEndpoint, ``chartOriginalTarget] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Literal scalar-extension simplex endpoint charts use only standard foundations."

end MotivicTest.ScalarExtensionSimplexEndpoint
