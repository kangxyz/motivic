module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.Common.GraphIdeal
/-! # The actual common compactification is covered by retained overlap and full boundary -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y S X : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) (α : X ⟶ S) (B : Type u) [CommRing B] (s : Spec (.of B) ⟶ S)

omit [IsSeparated p] in
/-- The full zero-boundary component is an actual pullback, including its nilpotents. -/
theorem commonZeroInclusion_isPullback :
    IsPullback (pullback.snd (commonSourceProjection k p r α)
      (s ≫ (r ≫ inclusion k p) ≫ projection k p))
      (commonZeroInclusion k p r α B s) (s ≫ r ≫ inclusion k p)
      (pullback.snd (commonSourceProjection k p r α) (projection k p)) := by
  have H : IsPullback
      (pullback.snd (commonSourceProjection k p r α)
        (s ≫ (r ≫ inclusion k p) ≫ projection k p))
      (pullback.fst _ _) ((s ≫ r ≫ inclusion k p) ≫ projection k p)
      (commonSourceProjection k p r α) := by
    simpa only [Category.assoc] using
      (IsPullback.of_hasPullback (commonSourceProjection k p r α)
        (s ≫ (r ≫ inclusion k p) ≫ projection k p)).flip
  convert H.of_bot' (IsPullback.of_hasPullback (commonSourceProjection k p r α)
    (projection k p)).flip using 1
  apply pullback.hom_ext <;> simp [commonZeroInclusion]

private theorem range_coprod_desc {D Z C : Scheme.{u}} (i : D ⟶ C) (j : Z ⟶ C) :
    Set.range (coprod.desc i j) = Set.range i ∪ Set.range j := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨y | y, rfl⟩ := (coprodMk D Z).surjective y
    · rw [coprodMk_inl]
      exact Or.inl ⟨y, by simp [← Scheme.Hom.comp_apply]⟩
    · rw [coprodMk_inr]
      exact Or.inr ⟨y, by simp [← Scheme.Hom.comp_apply]⟩
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨(coprod.inl : D ⟶ D ⨿ Z) y, by simp [← Scheme.Hom.comp_apply]⟩
    · exact ⟨(coprod.inr : Z ⟶ D ⨿ Z) y, by simp [← Scheme.Hom.comp_apply]⟩

theorem range_commonBoundaryInclusion :
    Set.range (commonBoundaryInclusion k p r α B s) =
      (pullback.snd (commonSourceProjection k p r α) (projection k p)) ⁻¹'
        (Set.range (infinityInclusion k p) ∪ Set.range (s ≫ r ≫ inclusion k p)) := by
  rw [commonBoundaryInclusion, range_coprod_desc, Set.preimage_union]
  congr 1
  · exact Scheme.Pullback.range_fst _ _
  · let H := commonZeroInclusion_isPullback k p r α B s
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨(pullback.snd (commonSourceProjection k p r α)
        (s ≫ (r ≫ inclusion k p) ≫ projection k p)) v,
        congrArg (fun m => m v) H.w⟩
    · rintro ⟨v, hv⟩
      obtain ⟨w, _, hw⟩ := Scheme.exists_preimage_of_isPullback H v x hv
      exact ⟨w, hw⟩

/-- No additional target points are discarded: the complement is precisely the whole boundary. -/
theorem commonBoundary_retained_cover
    (U : (Spec (.of (Polynomial k))).Opens) (z : Spec (.of B) ⟶ Spec (.of (Polynomial k)))
    (H : IsPullback (s ≫ r) (𝟙 _) p z)
    (hz : Set.range z = (U : Set (Spec (.of (Polynomial k))))ᶜ) :
    ∀ x : commonAmbient k p r α,
      x ∈ Set.range (constantRetainedInclusion k p U (commonSourceProjection k p r α)) ∨
        x ∈ Set.range (commonBoundaryInclusion k p r α B s) := by
  intro x
  rw [range_constantRetainedInclusion_complement k p U _ z (s ≫ r) H hz,
    range_commonBoundaryInclusion]
  exact Classical.em _ |>.symm
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
