/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.FreeSheafMonomorphisms

/-!
# Consumers of monomorphisms of free abelian sheaves

These tests retain independent site-object, hom and coefficient universes.
The geometric consumer retains the `u + 1` coefficient universe of the smooth
Nisnevich sheaf-cohomology construction.
-/

@[expose] public noncomputable section

universe t v u

open CategoryTheory AlgebraicGeometry Motivic Motivic.Hypercohomology

section Site

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}] {X Y : C} (f : X ⟶ Y) [Mono f]

example (Z : Cᵒᵖ) : Function.Injective ((uliftYoneda.{t}.map f).app Z) :=
  uliftYoneda_map_app_injective f Z

example : Mono (uliftYoneda.{t}.map f) := inferInstance

example : Mono ((freeAbelianSheafFunctor.{t, v, u} J).map f) := inferInstance

example : Mono ((freeAbelianSheafFunctor.{t, v, u} J).map f) :=
  freeAbelianSheafFunctor_map_mono J f

end Site

section SmoothSite

variable {S : Scheme.{u}} (J : GrothendieckTopology (SmoothSite S))
  [HasSheafify J AddCommGrpCat.{u + 1}]
  {U X : SmoothSite S} (j : U ⟶ X) [IsOpenImmersion j.left]

example : Mono j := smoothSite_mono_of_isOpenImmersion j

example : Mono ((freeAbelianSheafFunctor.{u + 1, u, u + 1} J).map j) :=
  freeAbelianSheafFunctor_map_mono_of_isOpenImmersion J j

end SmoothSite
