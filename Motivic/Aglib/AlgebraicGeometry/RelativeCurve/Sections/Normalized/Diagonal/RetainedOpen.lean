/-
Copyright (c) 2026 Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.Normalized.Diagonal.SectionPair
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.RetainedTarget

/-! # The full diagonal boundary and the actual original overlap open cover -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification

private theorem range_coprod_desc {D Z C : Scheme.{u}} (i : D ⟶ C) (j : Z ⟶ C) :
    Set.range (coprod.desc i j) = Set.range i ∪ Set.range j := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨y | y, rfl⟩ := (coprodMk D Z).surjective y
    · rw [coprodMk_inl]
      left
      exact ⟨y, by simp [← Scheme.Hom.comp_apply]⟩
    · rw [coprodMk_inr]
      right
      exact ⟨y, by simp [← Scheme.Hom.comp_apply]⟩
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨(coprod.inl : D ⟶ D ⨿ Z) y, by simp [← Scheme.Hom.comp_apply]⟩
    · exact ⟨(coprod.inr : Z ⟶ D ⨿ Z) y, by simp [← Scheme.Hom.comp_apply]⟩

variable (k : Type u) [Field k] {Y S Z : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) (s : Z ⟶ S)

/-- The two-component boundary is the entire inverse image of infinity and original Z. -/
theorem range_diagonalBoundaryMap : Set.range (diagonalBoundaryMap k p r s) =
    (pullback.snd ((r ≫ inclusion k p) ≫ projection k p) (projection k p)) ⁻¹'
      (Set.range (infinityInclusion k p) ∪ Set.range (s ≫ r ≫ inclusion k p)) := by
  rw [diagonalBoundaryMap, Hom.fullBoundaryProductMap, range_coprod_desc,
    Set.preimage_union]
  congr 1
  · exact Scheme.Pullback.range_fst _ _
  · let H := Hom.graphBoundaryRestriction_isPullback (projection k p) (r ≫ inclusion k p) s
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨(pullback.snd ((r ≫ inclusion k p) ≫ projection k p)
        (s ≫ (r ≫ inclusion k p) ≫ projection k p)) v, (congrArg (fun m => m v) H.w).symm⟩
    · rintro ⟨v, hv⟩
      obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback H x v hv.symm
      exact ⟨w, hw⟩

/-- The actual retained target open and full boundary cover the constant compactification. -/
theorem diagonalBoundary_retained_cover
    (U : (Spec (.of (Polynomial k))).Opens) (z : Z ⟶ Spec (.of (Polynomial k)))
    (H : IsPullback (s ≫ r) (𝟙 _) p z)
    (hz : Set.range z = (U : Set (Spec (.of (Polynomial k))))ᶜ) :
    ∀ x : diagonalAmbient k p r,
      x ∈ Set.range (constantRetainedInclusion k p U ((r ≫ inclusion k p) ≫ projection k p)) ∨
        x ∈ Set.range (diagonalBoundaryMap k p r s) := by
  intro x
  rw [range_constantRetainedInclusion_complement k p U _ z (s ≫ r) H hz,
    range_diagonalBoundaryMap]
  simp only [Category.assoc]
  exact Classical.em _ |>.symm
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
