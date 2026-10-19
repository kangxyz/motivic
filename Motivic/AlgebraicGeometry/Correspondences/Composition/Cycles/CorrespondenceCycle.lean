/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.IntegralCycle
public import Motivic.AlgebraicGeometry.Correspondences.Generators.Basic

/-!
# Faithful cycle representations of finite correspondences

This file embeds the existing geometric finite-correspondence generators and
cycle groups into integral closed-subscheme cycles and generic-point cycles.
Both embeddings preserve the literal coefficients and are injective. It does
not assert that an arbitrary pushforward preserves correspondence support.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

variable {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

/-- Forget only the finite-correspondence support condition, retaining the actual ideal sheaf. -/
noncomputable def toIntegralClosedSubscheme (V : FiniteCorrespondenceGenerator f g) :
    IntegralClosedSubscheme (pullback f g) := ⟨V.val, V.property.1⟩

theorem toIntegralClosedSubscheme_injective :
    Function.Injective (toIntegralClosedSubscheme (f := f) (g := g)) := by
  intro V W h
  apply Subtype.ext
  exact congrArg (fun V : IntegralClosedSubscheme (pullback f g) => V.val) h

/-- The embedded generic point of the actual correspondence support. -/
noncomputable def point (V : FiniteCorrespondenceGenerator f g) : (pullback (C := Scheme) f g) :=
  V.toIntegralClosedSubscheme.point

theorem point_injective : Function.Injective (point (f := f) (g := g)) :=
  IntegralClosedSubscheme.point_injective.comp toIntegralClosedSubscheme_injective

end FiniteCorrespondenceGenerator

namespace FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme

/-- The faithful additive inclusion into actual integral closed-subscheme cycles. -/
noncomputable def toIntegralCycle : FiniteCorrespondence f g →+ IntegralCycle (pullback f g) :=
  Finsupp.mapDomain.addMonoidHom FiniteCorrespondenceGenerator.toIntegralClosedSubscheme

@[simp]
theorem toIntegralCycle_single (V : FiniteCorrespondenceGenerator f g) (n : ℤ) :
    toIntegralCycle (Finsupp.single V n) = Finsupp.single V.toIntegralClosedSubscheme n :=
  Finsupp.mapDomain_single

theorem toIntegralCycle_injective :
    Function.Injective (toIntegralCycle (f := f) (g := g)) :=
  Finsupp.mapDomain_injective FiniteCorrespondenceGenerator.toIntegralClosedSubscheme_injective

/-- The faithful generic-point representation of finite-correspondence cycles. -/
noncomputable def toPoints : FiniteCorrespondence f g →+ FiniteSupportCycle (pullback f g) :=
  IntegralCycle.toPoints.comp toIntegralCycle

@[simp]
theorem toPoints_single (V : FiniteCorrespondenceGenerator f g) (n : ℤ) :
    toPoints (Finsupp.single V n) = Finsupp.single V.point n := by
  simp [toPoints, FiniteCorrespondenceGenerator.point]

theorem toPoints_injective : Function.Injective (toPoints (f := f) (g := g)) :=
  IntegralCycle.toPoints_injective.comp toIntegralCycle_injective

/-- A geometric multiplicity-one correspondence remains literally multiplicity one. -/
@[simp]
theorem toPoints_cycle (V : FiniteCorrespondenceGenerator f g) :
    toPoints V.cycle = Finsupp.single V.point 1 := toPoints_single V 1

end FiniteCorrespondence

end Motivic
