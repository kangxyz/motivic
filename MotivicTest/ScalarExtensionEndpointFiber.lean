/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.BaseChange.PolynomialFiber

/-!
# Consumers of the whole scalar-restricted endpoint fiber

These statements use arbitrary field maps and arbitrary source schemes.
There is no separability, source smoothness, or endpoint reducedness assumption.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve
open AlgebraicGeometry.ScalarExtensionEndpointFiber
open scoped Polynomial

universe u

namespace MotivicTest.ScalarExtensionEndpointFiber

variable {k E : Type u} [Field k] [Field E] (c : k →+* E)
  {C : Scheme.{u}} (f : C ⟶ Spec (.of E[X]))

/-- The zero endpoint remains the whole original zero fiber. -/
def zeroFiberIso : fiber (f ≫ coefficientMap c) (0 : k) ≅ fiber f (0 : E) := by
  simpa only [map_zero] using fiberIso c f (0 : k)

/-- The one endpoint remains the whole original one fiber. -/
def oneFiberIso : fiber (f ≫ coefficientMap c) (1 : k) ≅ fiber f (1 : E) := by
  simpa only [map_one] using fiberIso c f (1 : k)

/-- Every original source map commutes with the comparison. -/
theorem originalSourceMap (a : k) {T : Scheme.{u}} (g : C ⟶ T) :
    (fiberIso c f a).hom ≫ fiberInclusion f (c a) ≫ g =
      fiberInclusion (f ≫ coefficientMap c) a ≫ g :=
  fiberIso_hom_inclusion_assoc c f a g

/-- Signed endpoint cycles keep their actual original map into the target. -/
theorem signedEndpointCycle [IsNoetherian C]
    {T : Scheme.{u}} (g : C ⟶ T) [IsFinite g] (a : k) (n : ℤ) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberInclusion (f ≫
        coefficientMap c) a ≫ g)
        (n • _root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (f ≫ coefficientMap c) a)) =
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberInclusion f (c a) ≫ g)
        (n • _root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber f (c a))) := by
  simp only [map_zsmul, finitePushforward_fiberInclusion]

open Lean in
run_cmd do
  for name in #[
      ``evaluation_square, ``evaluation_isPushout, ``endpoint_isPullback,
      ``fiber_isPullback, ``fiberIso, ``fiberIso_hom_inclusion,
      ``fiberIso_inv_inclusion, ``fiberIso_inv_scalar, ``fiberIso_hom_scalar,
      ``finitePushforward_fiberIso, ``finitePushforward_fiberInclusion,
      ``zeroFiberIso, ``oneFiberIso, ``originalSourceMap, ``signedEndpointCycle] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole scalar-restricted endpoint fibers use only standard foundations."

end MotivicTest.ScalarExtensionEndpointFiber
