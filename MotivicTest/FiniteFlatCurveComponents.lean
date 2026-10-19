/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.FiniteFlat.Components

/-!
# Consumers of finite flat curve components

The whole source may be nonreduced and disconnected. The original finite flat
map alone proves flatness of every literal reduced component projection.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Polynomial

universe u

namespace MotivicTest.FiniteFlatCurveComponents
open _root_.AlgebraicGeometry.Scheme (IntegralClosedSubscheme)

/-- The consumer retains the unreduced ambient scheme and the actual inclusion. -/
theorem arbitraryFiniteFlatCurveComponent
    {k : Type u} [Field k] {P : Scheme.{u}}
    (f : P ⟶ Spec (.of k[X])) [IsFinite f] [Flat f] (z : genericPoints P) :
    Flat ((IntegralClosedSubscheme.pointClosure z.val).val.subschemeι ≫ f) :=
  _root_.AlgebraicGeometry.Scheme.Hom.finiteFlatCurve_component_flat f z

open Lean in
run_cmd do
  for name in #[``_root_.AlgebraicGeometry.Scheme.Hom.finiteCurve_flat_of_integral_surjective,
      ``_root_.AlgebraicGeometry.Scheme.Hom.finiteFlatCurve_component_flat,
          ``arbitraryFiniteFlatCurveComponent] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Finite flat curve components use only standard foundations."

end MotivicTest.FiniteFlatCurveComponents
