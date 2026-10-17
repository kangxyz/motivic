/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.UliftYonedaMono
public import Motivic.AlgebraicGeometry.SmoothSite
public import Motivic.Cohomology.Hypercohomology
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Monomorphisms of actual free abelian sheaves

The free abelian sheaf functor used to represent ordinary sheaf cohomology
preserves monomorphisms: universe-lifted Yoneda and the objectwise free abelian
group functor preserve them, and sheafification is left exact.

For the actual smooth site, an open immersion of underlying schemes is first
a monomorphism in the site, by its faithful forgetful functor. Its actual free
abelian sheaf map is therefore a monomorphism. No subcanonicity assumption or
change of coefficient universe is required.
-/

@[expose] public noncomputable section

universe t v u

open CategoryTheory AlgebraicGeometry

namespace Motivic.Hypercohomology

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

section SmoothSite

variable {S : Scheme.{u}} {U X : SmoothSite S}

/-- An open immersion of underlying schemes is a monomorphism in the actual smooth site. -/
theorem smoothSite_mono_of_isOpenImmersion (j : U ⟶ X) [IsOpenImmersion j.left] :
    Mono j := by
  have : Mono ((SmoothSite.forgetScheme S).map j) := inferInstanceAs (Mono j.left)
  exact (SmoothSite.forgetScheme S).mono_of_mono_map this

/-- An open immersion in the smooth site induces a mono of actual free abelian sheaves. -/
theorem freeAbelianSheafFunctor_map_mono_of_isOpenImmersion
    (J : GrothendieckTopology (SmoothSite S))
    [HasSheafify J AddCommGrpCat.{max u t}]
    (j : U ⟶ X) [IsOpenImmersion j.left] :
    Mono ((freeAbelianSheafFunctor.{t, u, u + 1} J).map j) := by
  have := smoothSite_mono_of_isOpenImmersion j
  exact freeAbelianSheafFunctor_map_mono J j

end SmoothSite

end Motivic.Hypercohomology
