/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.UliftYonedaMono
public import Aglib.CategoryTheory.Sites.Hypercohomology.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Free-sheaf monomorphisms on a site
-/

@[expose] public noncomputable section
universe t v u
open CategoryTheory
namespace CategoryTheory.Sheaf.Hypercohomology
section Site

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]

/-- The actual free abelian sheaf functor preserves monomorphisms. -/
instance freeAbelianSheafFunctor_preservesMonomorphisms :
    (freeAbelianSheafFunctor.{t, v, u} J).PreservesMonomorphisms := by
  unfold freeAbelianSheafFunctor
  infer_instance

/-- A monomorphism in the site induces a monomorphism of its actual free abelian sheaves. -/
theorem freeAbelianSheafFunctor_map_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    Mono ((freeAbelianSheafFunctor.{t, v, u} J).map f) := inferInstance

end Site

end CategoryTheory.Sheaf.Hypercohomology
