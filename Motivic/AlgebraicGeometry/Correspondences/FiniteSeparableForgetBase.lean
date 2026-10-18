/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ForgetBaseComposition
public import Motivic.AlgebraicGeometry.Correspondences.ForgetBaseGraph
public import Motivic.AlgebraicGeometry.Correspondences.GraphFunctor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The actual finite separable forget-base functor on correspondences

The direction is Cor L to Cor k. Objects keep their underlying scheme, and
morphisms keep the original signed supports inside the larger product.
Composition is proved by original Tor coefficients and finite pushforward;
identity and graph maps are the original componentwise graphs.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.Cor

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

local notation "r" => SmoothSite.finiteSeparableBaseMap k L
local notation "F" => SmoothSite.finiteSeparableForgetBase k L

/-- Finite separable forgetting uses the original correspondence category and composition. -/
def finiteSeparableForgetBase : Cor L ⥤ Cor k where
  obj X := ⟨(F).obj X.toSmoothSite⟩
  map {X Y} α := FiniteCorrespondence.forgetBase r X.toSmoothSite.hom Y.toSmoothSite.hom α
  map_id X := by
    exact FiniteCorrespondence.forgetBase_componentGraphCycleOver r
      (𝟙 X.toSmoothSite.left) (Category.id_comp X.toSmoothSite.hom)
  map_comp α β := FiniteCorrespondence.forgetBase_incidenceTorPairing k L α β

instance finiteSeparableForgetBase_additive : (finiteSeparableForgetBase k L).Additive where
  map_add := by
    intro X Y α β
    exact map_add (FiniteCorrespondence.forgetBase r X.toSmoothSite.hom Y.toSmoothSite.hom) α β

/-- The functor retains the actual signed finite-image map. -/
@[simp]
theorem finiteSeparableForgetBase_map {X Y : Cor L} (α : X ⟶ Y) :
    (finiteSeparableForgetBase k L).map α =
      FiniteCorrespondence.forgetBase r X.toSmoothSite.hom Y.toSmoothSite.hom α := rfl

/-- Original graph maps are preserved for every ordinary smooth-site morphism. -/
theorem finiteSeparableForgetBase_graph {X Y : SmoothSite (Spec (.of L))} (a : X ⟶ Y) :
    (finiteSeparableForgetBase k L).map ((graphFunctor L).map a) =
      (graphFunctor k).map ((F).map a) :=
  FiniteCorrespondence.forgetBase_componentGraphCycleOver r a.left (MorphismProperty.Over.w a)

/-- The bundled additive functor carries precisely the same original action. -/
def finiteSeparableForgetBaseAdditiveFunctor : Cor L ⥤+ Cor k :=
  AdditiveFunctor.of (finiteSeparableForgetBase k L)

end Motivic.Cor
