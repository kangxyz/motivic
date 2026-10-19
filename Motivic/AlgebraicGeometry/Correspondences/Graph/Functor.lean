/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Basic
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Components.Composition

/-!
# The actual graph functor from smooth schemes to finite correspondences

Each morphism is sent to the sum of its actual integral graph components.
The componentwise diagonal is the categorical identity, and the proved genuine
incidence Tor calculation supplies preservation of composition. The construction
works over an arbitrary field and allows disconnected and empty smooth objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.Cor
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

local instance (T : SmoothSite (Spec (.of k))) : IsNoetherian ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsNoetherian T.left)

local instance (T : SmoothSite (Spec (.of k))) : IsReduced ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsReduced T.left)

/-- Send an ordinary smooth-site morphism to its actual componentwise graph cycle. -/
def graphFunctor : SmoothSite (Spec (.of k)) ⥤ Cor k where
  obj X := ⟨X⟩
  map φ := componentGraphCycleOver φ.left (MorphismProperty.Over.w φ)
  map_id X := rfl
  map_comp {X Y Z} φ ψ := by
    exact (incidenceTorPairing_componentGraph_comp k φ.left (MorphismProperty.Over.w φ)
      ψ.left (MorphismProperty.Over.w ψ)).symm

@[simp]
theorem graphFunctor_obj (X : SmoothSite (Spec (.of k))) :
    (graphFunctor k).obj X = Cor.mk X := rfl

/-- The graph functor uses the actual graph cycle, rather than a formal generator. -/
theorem graphFunctor_map {X Y : SmoothSite (Spec (.of k))} (φ : X ⟶ Y) :
    (graphFunctor k).map φ = componentGraphCycleOver φ.left (MorphismProperty.Over.w φ) := rfl

end Motivic.Cor
