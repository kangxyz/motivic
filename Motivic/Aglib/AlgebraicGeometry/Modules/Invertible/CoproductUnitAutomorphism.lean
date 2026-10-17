/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.CoproductTrivialization

/-! # Exact unit automorphisms prescribed independently on disjoint components -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- An actual unit automorphism with identity on infinity and a specified unit on Z. -/
theorem exists_coprod_unitAutomorphism (D Z : Scheme.{u})
    (r : SheafOfModules.unit Z.ringCatSheaf ≅ SheafOfModules.unit Z.ringCatSheaf) :
    ∃ E : SheafOfModules.unit (D ⨿ Z).ringCatSheaf ≅
        SheafOfModules.unit (D ⨿ Z).ringCatSheaf,
      (restrictFunctor (coprod.inl : D ⟶ D ⨿ Z)).map E.hom = 𝟙 _ ∧
      (restrictFunctor (coprod.inr : Z ⟶ D ⨿ Z)).map E.hom ≫
        (restrictUnitIso _).hom = (restrictUnitIso _).hom ≫ r.hom := by
  let A : Bool → Scheme.{u} := fun b => cond b D Z
  let a : ∀ b, A b ⟶ D ⨿ Z := fun b => by
    cases b
    · exact coprod.inr
    · exact coprod.inl
  have hopen : ∀ b, IsOpenImmersion (a b) := by
    intro b; cases b <;> dsimp [a] <;> infer_instance
  let (b : Bool) : IsOpenImmersion (a b) := hopen b
  let O : (D ⨿ Z).Modules := SheafOfModules.unit (D ⨿ Z).ringCatSheaf
  let e : ∀ b, O.restrict (a b) ≅ O.restrict (a b) := fun b => by
    cases b
    · exact restrictUnitIso _ ≪≫ r ≪≫ (restrictUnitIso _).symm
    · exact Iso.refl _
  obtain ⟨E, hE⟩ := InternalHom.exists_iso_of_disjoint_restrictions A a (by
    intro x
    obtain ⟨x | x, rfl⟩ := (AlgebraicGeometry.coprodMk D Z).surjective x
    · exact ⟨true, x, (AlgebraicGeometry.coprodMk_inl D Z x).symm⟩
    · exact ⟨false, x, (AlgebraicGeometry.coprodMk_inr D Z x).symm⟩) (by
    intro b c hbc
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact (AlgebraicGeometry.isCompl_opensRange_inl_inr D Z).disjoint.symm
    · exact (AlgebraicGeometry.isCompl_opensRange_inl_inr D Z).disjoint
    · exact (hbc rfl).elim) O O e
  refine ⟨E, hE true, ?_⟩
  have h := hE false
  change (restrictFunctor (coprod.inr : Z ⟶ D ⨿ Z)).map E.hom =
    (restrictUnitIso _).hom ≫ r.hom ≫ (restrictUnitIso _).inv at h
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Modules
