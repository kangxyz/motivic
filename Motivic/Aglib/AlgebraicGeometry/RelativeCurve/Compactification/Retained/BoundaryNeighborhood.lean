/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # The full retained-curve boundary becomes finite near a whole good fiber

The retained open may be the actual principal affine smooth neighborhood. The
old compactification infinity controls its entire new boundary on the selected
fiber. Properness, not closedness of an affine critical image, then supplies the
base neighborhood. Arbitrary nonreduced closed boundaries are allowed.
-/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve
variable {C S B D : Scheme.{u}} (q : C ⟶ S) (b : B ⟶ C)
  [IsFinite (b ≫ q)] (U V : C.Opens)

/-- The new missing fiber lies in the image of the old finite infinity fiber. -/
theorem finite_retained_complement_fiber
    (hboundary : (U : Set C)ᶜ ⊆ Set.range b) (s : S)
    (hwhole : ∀ x : C, q x = s → x ∈ U → x ∈ V) :
    ((q ⁻¹' {s}) ∩ (V : Set C)ᶜ).Finite := by
  apply (((b ≫ q).finite_preimage_singleton s).image b).subset
  rintro x ⟨hx, hxV⟩
  have hxU : x ∉ U := fun hxU => hxV (hwhole x hx hxU)
  obtain ⟨y, rfl⟩ := hboundary hxU
  exact ⟨y, hx, rfl⟩

/-- Any actual closed boundary supported outside the retained open is finite
after one base shrink. In particular its original nilpotents are not discarded. -/
theorem exists_finite_closed_retained_boundary [IsProper q]
    (hboundary : (U : Set C)ᶜ ⊆ Set.range b) (s : S)
    (hwhole : ∀ x : C, q x = s → x ∈ U → x ∈ V)
    (i : D ⟶ C) [IsClosedImmersion i] (hi : Set.range i ⊆ (V : Set C)ᶜ) :
    ∃ T : S.Opens, s ∈ T ∧ IsFinite ((i ≫ q) ∣_ T) := by
  apply exists_isFinite_morphismRestrict_of_finite_preimage_singleton
  have hf := finite_retained_complement_fiber q b U V hboundary s hwhole
  have hp : (i ⁻¹' ((q ⁻¹' {s}) ∩ (V : Set C)ᶜ)).Finite :=
    hf.preimage i.isClosedEmbedding.injective.injOn
  apply hp.subset
  intro x hx
  exact ⟨hx, hi ⟨x, rfl⟩⟩

/-- The literal closed-complement ideal of the actual retained open. -/
def retainedBoundaryIdeal (V : C.Opens) : C.IdealSheafData :=
  IdealSheafData.vanishingIdeal ⟨(V : Set C)ᶜ, V.isOpen.isClosed_compl⟩

/-- The entire closed complement of the unchanged retained open. -/
abbrev retainedBoundary (V : C.Opens) := (retainedBoundaryIdeal V).subscheme

/-- Its native closed immersion into the original compactification. -/
abbrev retainedBoundaryInclusion (V : C.Opens) : retainedBoundary V ⟶ C :=
  (retainedBoundaryIdeal V).subschemeι

/-- The constructed boundary has exactly the complete missing-open support. -/
theorem range_retainedBoundaryInclusion :
    Set.range (retainedBoundaryInclusion V) = (V : Set C)ᶜ := by
  rw [IdealSheafData.range_subschemeι]
  simp [retainedBoundaryIdeal]

/-- The actual full closed complement is produced and finite over a genuine base open. -/
theorem exists_finite_retainedBoundary [IsProper q]
    (hboundary : (U : Set C)ᶜ ⊆ Set.range b) (s : S)
    (hwhole : ∀ x : C, q x = s → x ∈ U → x ∈ V) :
    ∃ T : S.Opens, s ∈ T ∧ IsFinite ((retainedBoundaryInclusion V ≫ q) ∣_ T) := by
  apply exists_finite_closed_retained_boundary q b U V hboundary s hwhole
  exact (range_retainedBoundaryInclusion V).le

end AlgebraicGeometry.Scheme.RelativeCurve
