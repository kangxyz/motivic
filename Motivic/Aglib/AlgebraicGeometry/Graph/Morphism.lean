/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The actual graph into a relative product

Intended upstream module: `Aglib.AlgebraicGeometry.Graph.Morphism`.
The graph and projection laws apply to arbitrary schemes and scheme morphisms.
Separatedness of the target structure map gives the original closed-immersion instance.
Current consumers are graph pair stalk maps and finite-correspondence generators.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Graph

variable {S X Y : Scheme.{u}} (φ : X ⟶ Y) (g : Y ⟶ S)

/-- The actual graph morphism into the fiber product. -/
noncomputable def correspondenceGraph : X ⟶ pullback (φ ≫ g) g :=
  pullback.lift (𝟙 X) φ (Category.id_comp (φ ≫ g))

@[reassoc (attr := simp)]
theorem correspondenceGraph_fst : correspondenceGraph φ g ≫ pullback.fst (φ ≫ g) g = 𝟙 X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem correspondenceGraph_snd : correspondenceGraph φ g ≫ pullback.snd (φ ≫ g) g = φ :=
  pullback.lift_snd _ _ _

instance [IsSeparated g] : IsClosedImmersion (correspondenceGraph φ g) := by
  unfold correspondenceGraph
  infer_instance

end AlgebraicGeometry.Scheme.Graph
