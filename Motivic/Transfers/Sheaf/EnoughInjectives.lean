/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Exactness
public import Motivic.Aglib.CategoryTheory.AdditiveFunctorGrothendieck
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Enough injectives for actual sheaves with transfers

The additive presheaf category has exact filtered colimits and an actual
separator. Its left exact Nisnevich reflection passes both properties to the
actual additive category of sheaves with transfers. Mathlib's Grothendieck
category theorem then supplies enough injectives. No ordinary-cohomology
acyclicity of their underlying sheaves is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.SheafWithTransfers

variable (k : Type u) [Field k]

/-- The actual transfer-preserving Nisnevich adjunction is a reflection. -/
instance forget_reflective : Reflective (forget.{u + 1} k) where
  L := PresheafWithTransfers.nisnevichSheafify k
  adj := PresheafWithTransfers.nisnevichSheafificationAdjunction k

/-- Colimits in transfer sheaves are obtained from the actual reflector. -/
instance hasColimitsOfSize : HasColimitsOfSize.{u + 1, u + 1}
    (SheafWithTransfers.{u + 1} k) :=
  hasColimits_of_reflective (forget.{u + 1} k)

/-- Filtered colimits are exact by left exactness of actual Nisnevich sheafification. -/
instance ab5OfSize : AB5OfSize.{u + 1, u + 1} (SheafWithTransfers.{u + 1} k) where
  ofShape J := (PresheafWithTransfers.nisnevichSheafificationAdjunction k).hasExactColimitsOfShape J

/-- A genuine separator descends from lifted additive representables. -/
instance hasSeparator : HasSeparator (SheafWithTransfers.{u + 1} k) :=
  HasSeparator.of_adjunction (PresheafWithTransfers.nisnevichSheafificationAdjunction k)

/-- The actual category of Nisnevich sheaves with transfers is Grothendieck abelian. -/
instance isGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1} (SheafWithTransfers.{u + 1} k) where

/-- Enough injectives is supplied by the genuine Grothendieck structure. -/
theorem enoughInjectives : EnoughInjectives (SheafWithTransfers.{u + 1} k) :=
  inferInstance

end Motivic.SheafWithTransfers
