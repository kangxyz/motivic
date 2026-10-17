/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ClosedImageBaseChange
public import Motivic.Aglib.AlgebraicGeometry.Cycles.FinitePushforwardInjective
public import Mathlib.Data.ZMod.Basic

/-!
# Actual ambient support base-change consumers

These checks retain the literal product maps and allow arbitrary base change.
The last consumer specializes the ambient base to the nonreduced scheme
`Spec (ZMod 4)`; no flatness or reducedness assumption is introduced.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ClosedImageBaseChange

universe u

variable {S X Y U C : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S) (u : U ⟶ S)
  (g : U ⟶ X) (hg : g ≫ x = u) (j : C ⟶ pullback x y)

example : IsPullback (pullback.fst (j ≫ pullback.fst x y) g)
    (inclusion x y u g hg j) j (ambientMap x y u g hg) :=
  inclusion_isPullback x y u g hg j

example : inclusion x y u g hg j ≫ pullback.fst u y =
    pullback.snd (j ≫ pullback.fst x y) g := inclusion_fst x y u g hg j

example [IsClosedImmersion j] : IsClosedImmersion (inclusion x y u g hg j) :=
  inferInstance

example [IsClosedImmersion j] (a b : Motivic.IntegralCycle
    (pullback (j ≫ pullback.fst x y) g))
    (h : Motivic.IntegralCycle.finitePushforward (inclusion x y u g hg j) a =
      Motivic.IntegralCycle.finitePushforward (inclusion x y u g hg j) b) : a = b :=
  Motivic.IntegralCycle.finitePushforward_injective_of_isClosedImmersion _ h

example {X Y U C : Scheme.{0}} (x : X ⟶ Spec (.of (ZMod 4)))
    (y : Y ⟶ Spec (.of (ZMod 4))) (g : U ⟶ X)
    (j : C ⟶ pullback x y) [IsClosedImmersion j] :
    IsClosedImmersion (inclusion x y (g ≫ x) g rfl j) := inferInstance

example : (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 := by decide

set_option linter.hashCommand false in
#print axioms AlgebraicGeometry.ClosedImageBaseChange.inclusion_isPullback
set_option linter.hashCommand false in
#print axioms AlgebraicGeometry.ClosedImageBaseChange.inclusion_isClosedImmersion
