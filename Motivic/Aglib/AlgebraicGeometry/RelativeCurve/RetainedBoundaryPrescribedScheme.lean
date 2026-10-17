/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.RetainedBoundaryNeighborhood
public import Motivic.Aglib.AlgebraicGeometry.NisnevichFiniteSplitting

/-! # One base shrink retains the full prescribed finite scheme and finite new boundary -/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve

set_option backward.isDefEq.respectTransparency.types false in
/-- A smaller actual base open preserves finiteness of the original restriction. -/
theorem finite_morphismRestrict_of_le {X S : Scheme.{u}} (f : X ⟶ S)
    {U V : S.Opens} (hVU : V ≤ U) [IsFinite (f ∣_ U)] : IsFinite (f ∣_ V) := by
  have h : IsFinite (f ∣_ U.ι ''ᵁ (U.ι ⁻¹ᵁ V)) :=
    (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
      (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))).mp
      inferInstance
  have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hVU
  exact he ▸ h

/-- The whole original finite prescribed scheme, including nilpotents, remains
inside the retained affine open over the same base neighborhood as the new boundary. -/
theorem exists_finite_retainedBoundary_preserving_scheme
    {C S B Z : Scheme.{u}} (q : C ⟶ S) [IsProper q] (b : B ⟶ C)
    [IsFinite (b ≫ q)] (U V : C.Opens)
    (hboundary : (U : Set C)ᶜ ⊆ Set.range b) (s : S)
    (hwhole : ∀ x : C, q x = s → x ∈ U → x ∈ V)
    (z : Z ⟶ C) [IsFinite (z ≫ q)] (hzU : Set.range z ⊆ U) :
    ∃ T : S.Opens, s ∈ T ∧ IsFinite ((retainedBoundaryInclusion V ≫ q) ∣_ T) ∧
      ∀ x : Z, (z ≫ q) x ∈ T → z x ∈ V := by
  obtain ⟨T₁, hs₁, hfinite⟩ := exists_finite_retainedBoundary q b U V hboundary s hwhole
  obtain ⟨T₂, hs₂, hdisj⟩ := exists_open_preimage_disjoint_of_isFinite (z ≫ q)
    ((z ⁻¹ᵁ V : Z.Opens) : Set Z)ᶜ (z ⁻¹ᵁ V).isOpen.isClosed_compl s (by
      intro x hx he
      exact hx (hwhole (z x) he (hzU ⟨x, rfl⟩)))
  have : IsFinite ((retainedBoundaryInclusion V ≫ q) ∣_ T₁) := hfinite
  refine ⟨T₁ ⊓ T₂, ⟨hs₁, hs₂⟩,
    finite_morphismRestrict_of_le _ inf_le_left, ?_⟩
  intro x hx
  by_contra hn
  exact Set.disjoint_left.mp hdisj hx.2 hn

end AlgebraicGeometry.Scheme.RelativeCurve
