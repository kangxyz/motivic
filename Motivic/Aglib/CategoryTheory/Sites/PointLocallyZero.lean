/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.Algebra.Category.Grp.Abelian

/-! # A locally zero abelian presheaf has zero actual point fibers -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u v w
namespace CategoryTheory.GrothendieckTopology.Point
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w}) (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})

/-- Local vanishing kills the actual colimit point fiber, without enough points. -/
theorem presheafFiber_isZero_of_locally_zero
    (hP : ∀ (X : C) (s : P.obj (op X)), Presheaf.equalizerSieve s 0 ∈ J X) :
    IsZero (Φ.presheafFiber.obj P) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Φ.presheafFiber_hom_ext
  intro X x
  simp only [Category.comp_id, Limits.comp_zero]
  ext s
  change Φ.toPresheafFiber X x P s = 0
  obtain ⟨Y, f, hf, y, hy⟩ := Φ.jointly_surjective _ (hP X s) x
  have hz : P.map f.op s = 0 := by
    change P.map f.op s = P.map f.op 0 at hf
    simpa only [map_zero] using hf
  have hw := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w f y P) s
  rw [hy] at hw
  simpa only [ConcreteCategory.comp_apply, hz, map_zero] using hw.symm

end CategoryTheory.GrothendieckTopology.Point
