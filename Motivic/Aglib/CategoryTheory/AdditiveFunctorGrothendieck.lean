/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.LiftedAdditiveYoneda

/-! # Additive abelian presheaves form a Grothendieck category

Exact filtered colimits are computed through the actual additive-functor
inclusion. A separator is the coproduct of lifted additive representables.
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.AdditiveFunctor

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- Additive abelian presheaves, with coefficient universe containing the source
objects and arrows, form a genuine Grothendieck abelian category. -/
instance isGrothendieckAbelian :
    IsGrothendieckAbelian.{max u v} (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v}) where

end CategoryTheory.AdditiveFunctor
