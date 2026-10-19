/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.DisjointBoundary.Restriction
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.DisjointBoundary.Basic

/-! # Gluing exact prescribed component trivializations on the full boundary -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Component trivializations glue on the actual pulled-back module, retaining their
literal restriction equations after the canonical comparison maps. -/
theorem exists_coprod_pullback_unitIso {D Z C : Scheme.{u}}
    (i : D ⟶ C) (j : Z ⟶ C) (M : C.Modules)
    (eD : (pullback i).obj M ≅ SheafOfModules.unit D.ringCatSheaf)
    (eZ : (pullback j).obj M ≅ SheafOfModules.unit Z.ringCatSheaf) :
    ∃ E : (pullback (coprod.desc i j)).obj M ≅ SheafOfModules.unit (D ⨿ Z).ringCatSheaf,
      (restrictFunctor (coprod.inl : D ⟶ D ⨿ Z)).map E.hom ≫
          (restrictUnitIso _).hom = (coprodPullbackRestrictLeft i j).hom.app M ≫ eD.hom ∧
      (restrictFunctor (coprod.inr : Z ⟶ D ⨿ Z)).map E.hom ≫
          (restrictUnitIso _).hom = (coprodPullbackRestrictRight i j).hom.app M ≫ eZ.hom := by
  let A : Bool → Scheme.{u} := fun b => cond b D Z
  let a : ∀ b, A b ⟶ D ⨿ Z := fun b => by
    cases b
    · exact coprod.inr
    · exact coprod.inl
  have hopen : ∀ b, IsOpenImmersion (a b) := by intro b; cases b <;> dsimp [a] <;> infer_instance
  let (b : Bool) : IsOpenImmersion (a b) := hopen b
  let e : ∀ b, ((pullback (coprod.desc i j)).obj M).restrict (a b) ≅
      (restrictFunctor (a b)).obj (SheafOfModules.unit (D ⨿ Z).ringCatSheaf) := fun b => by
    cases b
    · exact (coprodPullbackRestrictRight i j).app M ≪≫ eZ ≪≫ (restrictUnitIso _).symm
    · exact (coprodPullbackRestrictLeft i j).app M ≪≫ eD ≪≫ (restrictUnitIso _).symm
  obtain ⟨E, hE⟩ := InternalHom.exists_iso_of_disjoint_restrictions A a (by
    intro x
    obtain ⟨x | x, rfl⟩ := (AlgebraicGeometry.coprodMk D Z).surjective x
    · exact ⟨true, x, AlgebraicGeometry.coprodMk_inl D Z x |>.symm⟩
    · exact ⟨false, x, AlgebraicGeometry.coprodMk_inr D Z x |>.symm⟩) (by
    intro b c hbc
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact (AlgebraicGeometry.isCompl_opensRange_inl_inr D Z).disjoint.symm
    · exact (AlgebraicGeometry.isCompl_opensRange_inl_inr D Z).disjoint
    · exact (hbc rfl).elim) _ _ e
  refine ⟨E, ?_, ?_⟩
  · have h := hE true
    change (restrictFunctor (coprod.inl : D ⟶ D ⨿ Z)).map E.hom =
      (coprodPullbackRestrictLeft i j).hom.app M ≫ eD.hom ≫
        (restrictUnitIso (coprod.inl : D ⟶ D ⨿ Z)).inv at h
    rw [h]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · have h := hE false
    change (restrictFunctor (coprod.inr : Z ⟶ D ⨿ Z)).map E.hom =
      (coprodPullbackRestrictRight i j).hom.app M ≫ eZ.hom ≫
        (restrictUnitIso (coprod.inr : Z ⟶ D ⨿ Z)).inv at h
    rw [h]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
end AlgebraicGeometry.Scheme.Modules
