/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.AdditiveFunctorAbelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory

/-!
# Exact filtered colimits of additive functors

The inclusion of additive functors into the ordinary functor category preserves
colimits and finite limits, and reflects finite limits. Hence exactness of
colimits in the target passes to additive functor categories. In particular,
AB5 passes from an abelian target to its category of additive functors.
-/

@[expose] public noncomputable section

universe w w' v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D]

/-- Additive functors inherit all colimits of a given size from the target. -/
instance AdditiveFunctor.hasColimitsOfSize [Preadditive D] [HasColimitsOfSize.{w, w'} D] :
    HasColimitsOfSize.{w, w'} (C ⥤+ D) where
  has_colimits_of_shape _ := inferInstance

/-- Additive functors inherit filtered colimits of a given size from the target. -/
instance AdditiveFunctor.hasFilteredColimitsOfSize [Preadditive D]
    [HasFilteredColimitsOfSize.{w, w'} D] :
    HasFilteredColimitsOfSize.{w, w'} (C ⥤+ D) where
  HasColimitsOfShape _ := inferInstance

variable [Abelian D]

/-- Exactness of colimits is detected by the fully faithful inclusion. -/
instance AdditiveFunctor.hasExactColimitsOfShape (J : Type w') [Category.{w} J]
    [HasColimitsOfShape J D] [HasExactColimitsOfShape J D] :
    HasExactColimitsOfShape J (C ⥤+ D) :=
  HasExactColimitsOfShape.domain_of_functor J (AdditiveFunctor.forget C D)

/-- Filtered colimits of additive functors are exact when they are exact in the target. -/
instance AdditiveFunctor.ab5OfSize [HasFilteredColimitsOfSize.{w, w'} D]
    [AB5OfSize.{w, w'} D] : AB5OfSize.{w, w'} (C ⥤+ D) where
  ofShape _ := inferInstance

end CategoryTheory
