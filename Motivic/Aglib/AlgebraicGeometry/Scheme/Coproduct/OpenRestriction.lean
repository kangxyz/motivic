/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits

/-! # The literal inverse image of an open in a scheme coproduct

Intended upstream module: `Aglib.AlgebraicGeometry.Scheme.Coproduct.OpenRestriction`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.CoproductFrame`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- Restriction has the literal inverse image of the original range. -/
theorem range_morphismRestrict_eq_preimage {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) :
    Set.range (f ∣_ U) = U.ι ⁻¹' Set.range f := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, (morphismRestrict_base_coe f U y).symm⟩
  · rintro ⟨y, hy⟩
    have hm : y ∈ f ⁻¹ᵁ U := by
      change f y ∈ U
      rw [hy]
      exact x.2
    refine ⟨⟨y, hm⟩, ?_⟩
    apply Subtype.ext
    exact (morphismRestrict_base_coe f U ⟨y, hm⟩).trans hy

/-- The two actual inverse-image opens are a coproduct, with no reduced replacement. -/
def coprodOpenRestrictionIsColimit {D Z : Scheme.{u}} (W : (D ⨿ Z).Opens) :
    IsColimit (BinaryCofan.mk ((coprod.inl : D ⟶ D ⨿ Z) ∣_ W)
      ((coprod.inr : Z ⟶ D ⨿ Z) ∣_ W)) := by
  have hr : IsCompl
      (Set.range ((coprod.inl : D ⟶ D ⨿ Z) ∣_ W))
      (Set.range ((coprod.inr : Z ⟶ D ⨿ Z) ∣_ W)) := by
    rw [range_morphismRestrict_eq_preimage, range_morphismRestrict_eq_preimage]
    exact IsCompl.preimage W.ι (isCompl_range_inl_inr D Z)
  have hc : IsCompl
      ((coprod.inl : D ⟶ D ⨿ Z) ∣_ W).opensRange
      ((coprod.inr : Z ⟶ D ⨿ Z) ∣_ W).opensRange := by
    convert! hr
    simp only [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj]
    rfl
  exact (AlgebraicGeometry.nonempty_isColimit_binaryCofanMk_of_isCompl _ _ hc).some

/-- Canonical coproduct identification for any original open of the coproduct. -/
def coprodOpenRestrictionIso {D Z : Scheme.{u}} (W : (D ⨿ Z).Opens) :
    (((coprod.inl : D ⟶ D ⨿ Z) ⁻¹ᵁ W).toScheme ⨿
      ((coprod.inr : Z ⟶ D ⨿ Z) ⁻¹ᵁ W).toScheme) ≅ W.toScheme :=
  (coprodIsCoprod _ _).coconePointUniqueUpToIso (coprodOpenRestrictionIsColimit W)

@[reassoc (attr := simp)]
theorem coprodOpenRestrictionIso_inl {D Z : Scheme.{u}} (W : (D ⨿ Z).Opens) :
    coprod.inl ≫ (coprodOpenRestrictionIso W).hom = (coprod.inl : D ⟶ D ⨿ Z) ∣_ W := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom _
    (coprodOpenRestrictionIsColimit W) (Discrete.mk WalkingPair.left)

@[reassoc (attr := simp)]
theorem coprodOpenRestrictionIso_inr {D Z : Scheme.{u}} (W : (D ⨿ Z).Opens) :
    coprod.inr ≫ (coprodOpenRestrictionIso W).hom = (coprod.inr : Z ⟶ D ⨿ Z) ∣_ W := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom _
    (coprodOpenRestrictionIsColimit W) (Discrete.mk WalkingPair.right)

variable {D Z C S : Scheme.{u}} (π : C ⟶ S) (d : D ⟶ C) (z : Z ⟶ C) (O : S.Opens)

/-- Restrict the original two summands only along the same coefficient-base open. -/
def coprodBoundaryPreimageIso :
    (((d ≫ π) ⁻¹ᵁ O).toScheme ⨿ ((z ≫ π) ⁻¹ᵁ O).toScheme) ≅
      ((coprod.desc d z ≫ π) ⁻¹ᵁ O).toScheme :=
  coprod.mapIso
    (D.isoOfEq (show (d ≫ π) ⁻¹ᵁ O =
        (coprod.inl : D ⟶ D ⨿ Z) ⁻¹ᵁ ((coprod.desc d z ≫ π) ⁻¹ᵁ O) from by
      change (d ≫ π) ⁻¹ᵁ O = (coprod.inl ≫ coprod.desc d z ≫ π) ⁻¹ᵁ O
      rw [coprod.inl_desc_assoc]))
    (Z.isoOfEq (show (z ≫ π) ⁻¹ᵁ O =
        (coprod.inr : Z ⟶ D ⨿ Z) ⁻¹ᵁ ((coprod.desc d z ≫ π) ⁻¹ᵁ O) from by
      change (z ≫ π) ⁻¹ᵁ O = (coprod.inr ≫ coprod.desc d z ≫ π) ⁻¹ᵁ O
      rw [coprod.inr_desc_assoc])) ≪≫
    coprodOpenRestrictionIso ((coprod.desc d z ≫ π) ⁻¹ᵁ O)

@[reassoc]
theorem coprodBoundaryPreimageIso_hom_ι :
    (coprodBoundaryPreimageIso π d z O).hom ≫ ((coprod.desc d z ≫ π) ⁻¹ᵁ O).ι =
      coprod.desc (((d ≫ π) ⁻¹ᵁ O).ι ≫ coprod.inl)
        (((z ≫ π) ⁻¹ᵁ O).ι ≫ coprod.inr) := by
  apply coprod.hom_ext <;>
    simp [coprodBoundaryPreimageIso, Category.assoc, morphismRestrict_ι]

@[reassoc]
theorem coprodBoundaryPreimageIso_hom_map :
    (coprodBoundaryPreimageIso π d z O).hom ≫ ((coprod.desc d z ≫ π) ⁻¹ᵁ O).ι ≫
      coprod.desc d z =
      coprod.desc (((d ≫ π) ⁻¹ᵁ O).ι ≫ d) (((z ≫ π) ⁻¹ᵁ O).ι ≫ z) := by
  rw [coprodBoundaryPreimageIso_hom_ι_assoc, coprod.desc_comp]
  simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc]

end AlgebraicGeometry.Scheme
