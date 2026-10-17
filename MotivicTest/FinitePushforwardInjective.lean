/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.FinitePushforwardInjective
public import Mathlib.Data.ZMod.Basic
public import Lean.Util.CollectAxioms

/-!
# Closed-immersion cancellation for actual signed cycles

The consumers retain arbitrary coefficients and include closed subschemes of
a nonreduced ambient scheme. No smoothness, field or purity input is used.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.FinitePushforwardInjective

example {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (α β : IntegralCycle X)
    (h : IntegralCycle.finitePushforward f (α - β) = 0) : α = β := by
  apply sub_eq_zero.mp
  exact IntegralCycle.finitePushforward_injective_of_isClosedImmersion f
    (h.trans (map_zero _).symm)

example {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (A B : IntegralClosedSubscheme X) (h : A.finiteImage f = B.finiteImage f) : A = B :=
  IntegralClosedSubscheme.finiteImage_injective_of_isClosedImmersion f h

example (I : (Spec (.of (ZMod 4))).IdealSheafData)
    (α β : IntegralCycle I.subscheme)
    (h : IntegralCycle.finitePushforward I.subschemeι α =
      IntegralCycle.finitePushforward I.subschemeι β) : α = β :=
  IntegralCycle.finitePushforward_injective_of_isClosedImmersion I.subschemeι h

open Lean in
run_cmd do
  for name in #[``IntegralClosedSubscheme.finiteImage_injective_of_isClosedImmersion,
      ``IntegralCycle.finitePushforward_injective_of_isClosedImmersion] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.FinitePushforwardInjective
