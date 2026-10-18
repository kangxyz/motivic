/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Locally zero abelian presheaves have zero ordinary sheafification -/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite
open scoped ZeroObject

universe u v w

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Original sections locally equal to zero give the zero ordinary sheafification.
The topology and the canonical sheafification functor are unchanged. -/
theorem isZero_sheafify_of_locally_zero (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (hP : ∀ (X : C) (s : P.obj (op X)), equalizerSieve s 0 ∈ J X) :
    IsZero ((presheafToSheaf J AddCommGrpCat.{w}).obj P) := by
  let z : P ⟶ 0 := 0
  have hi : IsLocallyInjective J z := by
    constructor
    intro X x y _
    apply J.superset_covering (S := equalizerSieve (x - y) 0) _ (hP X.unop (x - y))
    intro U f hf
    change P.map f.op x = P.map f.op y
    change P.map f.op (x - y) = P.map f.op 0 at hf
    simpa only [map_sub, map_zero, sub_eq_zero] using hf
  have hs : IsLocallySurjective J z := by
    apply isLocallySurjective_of_surjective
    intro X x
    have hz : IsZero ((0 : Cᵒᵖ ⥤ AddCommGrpCat.{w}).obj X) :=
      ((evaluation _ _).obj X).map_isZero (isZero_zero _)
    have := AddCommGrpCat.subsingleton_of_isZero hz
    exact ⟨0, Subsingleton.elim _ _⟩
  have hz : IsIso ((presheafToSheaf J AddCommGrpCat.{w}).map z) :=
    (J.W_iff z).mp (J.W_of_isLocallyBijective z)
  exact ((presheafToSheaf J AddCommGrpCat.{w}).map_isZero (isZero_zero _)).of_iso
    (asIso ((presheafToSheaf J AddCommGrpCat.{w}).map z))

end CategoryTheory.Presheaf
