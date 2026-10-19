/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Generalizing.GenericPoints
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.QuasiFinite.GenericFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Motivic.Aglib.AlgebraicGeometry.Scheme.DomainStalkComponents
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.BaseChange.Generalizing

/-!
# Components under generalizing morphisms
-/

@[expose] public noncomputable section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Products
open _root_.AlgebraicGeometry.Scheme.Hom

set_option backward.isDefEq.respectTransparency false in
/-- Generalization lifting can be checked after restricting the target to an
open containing the whole image. -/
theorem generalizingMap_of_morphismRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (hU : Set.range f ⊆ U) (hf : GeneralizingMap (f ∣_ U)) : GeneralizingMap f := by
  intro x y hy
  have hxU : f x ∈ U := hU ⟨x, rfl⟩
  have hyU : y ∈ U := U.isOpen.stableUnderGeneralization hy hxU
  have hxy : (⟨y, hyU⟩ : U) ⤳ (f ∣_ U) ⟨x, hxU⟩ :=
    (subtype_specializes_iff _ _).mpr (by
      change y ⤳ ((f ∣_ U) ⟨x, hxU⟩).1
      rw [morphismRestrict_base_coe]
      exact hy)
  obtain ⟨x', hx', hx'y⟩ := hf hxy
  refine ⟨x'.1, (subtype_specializes_iff _ _).mp hx', ?_⟩
  simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hx'y

set_option backward.isDefEq.respectTransparency false in
/-- A finite integral support surjecting onto one actual clopen normal
component has generalizing finite-type base changes, even when the ambient
base and the test scheme are disconnected. -/
theorem generalizingMap_of_isPullback_component
    {W A B Y : Scheme.{u}} [IsNoetherian Y] [IsIntegral B]
    (p : W ⟶ A) (q : W ⟶ B) (g : A ⟶ Y) (f : B ⟶ Y)
    (H : IsPullback p q g f) [IsFinite f] [LocallyOfFiniteType g]
    (hf : Set.range f ∈ irreducibleComponents Y)
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y)) : GeneralizingMap p := by
  let U := domainStalkComponentOpen (fun y ↦ (hY y).1) (Set.range f) hf
  have : IsIntegral U.toScheme :=
    isIntegral_domainStalkComponentOpen (fun y ↦ (hY y).1) (Set.range f) hf
  have : Nonempty (f ⁻¹ᵁ U) := by
    obtain ⟨b⟩ := (inferInstance : Nonempty B)
    exact ⟨⟨b, ⟨b, rfl⟩⟩⟩
  have : IsIntegral (f ⁻¹ᵁ U).toScheme :=
    isIntegral_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  have : Surjective (f ∣_ U) := by
    constructor
    intro y
    obtain ⟨b, hb⟩ := y.2
    refine ⟨⟨b, ⟨b, rfl⟩⟩, Subtype.ext ?_⟩
    rw [morphismRestrict_base_coe]
    exact hb
  apply generalizingMap_of_morphismRestrict p (g ⁻¹ᵁ U)
  · rintro a ⟨w, rfl⟩
    change g (p w) ∈ Set.range f
    exact ⟨q w, (congrArg (fun e : W ⟶ Y ↦ e w) H.w).symm⟩
  · have H' := Scheme.Hom.isPullback_resLE H (US := U)
      (UT := f ⁻¹ᵁ U) (UX := g ⁻¹ᵁ U) le_rfl le_rfl
      (UY := p ⁻¹ᵁ g ⁻¹ᵁ U) (by
        rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage, inf_idem])
    simp only [Scheme.Hom.resLE_eq_morphismRestrict] at H'
    exact generalizingMap_of_isPullback_normal_base _ _ _ _ H'
      (isIntegrallyClosed_stalk_open_of_stalks (fun y ↦ (hY y).2) U)


end AlgebraicGeometry.Scheme.Products
