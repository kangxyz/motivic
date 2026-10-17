/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.FiniteBaseNeighborhood
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Whole-support line bundle frames near a finite proper fiber -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- Only the base is shrunk. A finite fiber of a proper support yields a frame on
its entire inverse image, preserving all nonreduced support data. -/
theorem exists_base_open_unitIso_of_isProper_finite_fiber
    {D S : Scheme.{u}} (f : D ⟶ S) [IsProper f] (x : S)
    (hx : (f ⁻¹' {x}).Finite) (L : LineBundle D) :
    ∃ O : S.Opens, x ∈ O ∧
      Nonempty ((Modules.restrictFunctor (f ⁻¹ᵁ O).ι).obj L.val ≅
        SheafOfModules.unit (f ⁻¹ᵁ O).toScheme.ringCatSheaf) := by
  obtain ⟨W, hxW, hfin⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f x hx
  let : IsFinite (f ∣_ W) := hfin
  let V := f ⁻¹ᵁ W
  let L' := pullbackLineBundle V.ι L
  obtain ⟨T, hxT, ⟨e⟩⟩ := exists_base_open_unitIso_of_isFinite
    (f ∣_ W) ⟨x, hxW⟩ L'
  let O := W.ι ''ᵁ T
  let Z := (f ∣_ W) ⁻¹ᵁ T
  let j := Z.ι ≫ V.ι
  let e' : (Modules.restrictFunctor j).obj L.val ≅
      SheafOfModules.unit Z.toScheme.ringCatSheaf :=
    (Modules.restrictFunctorComp Z.ι V.ι).app L.val ≪≫
      (Modules.restrictFunctor Z.ι).mapIso
        ((Modules.restrictFunctorIsoPullback V.ι).app L.val) ≪≫ e
  have hj : j.opensRange = f ⁻¹ᵁ O := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]
    exact image_morphismRestrict_preimage f W T
  have he : Nonempty ((Modules.restrictFunctor j.opensRange.ι).obj L.val ≅
      SheafOfModules.unit j.opensRange.toScheme.ringCatSheaf) :=
    ⟨restrictUnitIsoOnRange L.val j e'⟩
  rw [hj] at he
  exact ⟨O, ⟨⟨x, hxW⟩, hxT, rfl⟩, he⟩

end AlgebraicGeometry.Scheme.Modules.Invertible
