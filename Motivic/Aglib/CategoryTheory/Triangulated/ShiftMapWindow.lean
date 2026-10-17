/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.Algebra.Group.Int.Defs

/-! # Transport of a specified Hom map across shifts -/
@[expose] public section
open CategoryTheory
universe v₁ v₂ u₁ u₂
namespace CategoryTheory.Functor
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ]
  {A B : C} {Z : D} (c : F.obj B ⟶ Z) (n : ℤ)

/-- Commutation with shifts identifies the specified postcomposition map, not merely its groups. -/
theorem map_postcomp_shift (f : A ⟶ B) :
    F.map (f⟦n⟧') ≫ (F.commShiftIso n).hom.app B ≫ c⟦n⟧' =
      (F.commShiftIso n).hom.app A ≫ (F.map f ≫ c)⟦n⟧' := by
  rw [F.commShiftIso_hom_naturality_assoc, Functor.map_comp]

/-- Injectivity of an actual Hom map is invariant under simultaneous source and target shift. -/
theorem map_postcomp_shift_injective
    (h : Function.Injective (fun f : A ⟶ B => F.map f ≫ c)) :
    Function.Injective (fun f : A⟦n⟧ ⟶ B⟦n⟧ =>
      F.map f ≫ (F.commShiftIso n).hom.app B ≫ c⟦n⟧') := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := (shiftFunctor C n).map_surjective x
  obtain ⟨y, rfl⟩ := (shiftFunctor C n).map_surjective y
  dsimp only at hxy
  rw [F.map_postcomp_shift, F.map_postcomp_shift] at hxy
  have hh := (cancel_epi ((F.commShiftIso n).hom.app A)).mp hxy
  exact congrArg (fun f => (shiftFunctor C n).map f)
    (h ((shiftFunctor D n).map_injective hh))

/-- Bijectivity of the same actual Hom map is invariant under simultaneous shift. -/
theorem map_postcomp_shift_bijective
    (h : Function.Bijective (fun f : A ⟶ B => F.map f ≫ c)) :
    Function.Bijective (fun f : A⟦n⟧ ⟶ B⟦n⟧ =>
      F.map f ≫ (F.commShiftIso n).hom.app B ≫ c⟦n⟧') := by
  refine ⟨F.map_postcomp_shift_injective c n h.1, ?_⟩
  intro y
  obtain ⟨z, hz⟩ := (shiftFunctor D n).map_surjective
    ((F.commShiftIso n).inv.app A ≫ y)
  obtain ⟨x, rfl⟩ := h.2 z
  refine ⟨x⟦n⟧', ?_⟩
  dsimp only
  rw [F.map_postcomp_shift, hz]
  simp

omit [HasShift C ℤ] [HasShift D ℤ] [F.CommShift ℤ] in
/-- Changing the source by a specified isomorphism preserves the specified Hom-map injectivity. -/
theorem map_postcomp_isoSource_injective {A' : C} (e : A ≅ A')
    (h : Function.Injective (fun f : A ⟶ B => F.map f ≫ c)) :
    Function.Injective (fun f : A' ⟶ B => F.map f ≫ c) := by
  intro x y hxy
  apply (cancel_epi e.hom).mp
  apply h
  simpa only [Functor.map_comp, Category.assoc] using congrArg (F.map e.hom ≫ ·) hxy

omit [HasShift C ℤ] [HasShift D ℤ] [F.CommShift ℤ] in
/-- Changing the source by a specified isomorphism preserves the specified Hom-map bijectivity. -/
theorem map_postcomp_isoSource_bijective {A' : C} (e : A ≅ A')
    (h : Function.Bijective (fun f : A ⟶ B => F.map f ≫ c)) :
    Function.Bijective (fun f : A' ⟶ B => F.map f ≫ c) := by
  refine ⟨F.map_postcomp_isoSource_injective c e h.1, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := h.2 (F.map e.hom ≫ y)
  refine ⟨e.inv ≫ x, ?_⟩
  simp only [Functor.map_comp, Category.assoc, hx, Iso.map_inv_hom_id_assoc]

end CategoryTheory.Functor
