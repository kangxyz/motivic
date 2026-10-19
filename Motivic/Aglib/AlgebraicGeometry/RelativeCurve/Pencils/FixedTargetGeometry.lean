/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.FiniteChart.CompactificationChart
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.PencilMaps
/-! # The actual normalized source over one fixed target presentation

The source projective map is the composite of the finite normalization map with the
original target projective map. No second embedding or projection is selected.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
universe u
namespace AlgebraicGeometry.Scheme.EtaleCompactification
variable (R : Type u) [CommRing R] (ι : Type u)
  (X C : Scheme.{u})
  [IsIntegral C] [IsLocallyNoetherian C]
  [∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x)]
  {Y A Z D : Scheme.{u}}
  (p : Y ⟶ X) [Etale p] [QuasiCompact p] [IsSeparated p]
  (j : X ⟶ C) [IsOpenImmersion j] [QuasiCompact j]
  (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]

/-- The finite projective map is forced by the one fixed target map. -/
abbrev fixedTargetSourceProjectiveMap := (genericMap C (p ≫ j)).fromNormalization ≫ f

instance fixedTargetSourceProjectiveMap_finite :
    IsFinite (fixedTargetSourceProjectiveMap R ι X C p j f) := by
  dsimp [fixedTargetSourceProjectiveMap]
  infer_instance

omit [IsLocallyNoetherian C] [IsSeparated p] [IsFinite f] in
@[reassoc]
theorem fixedTargetSourceProjectiveMap_inclusion :
    inclusion C (p ≫ j) ≫ fixedTargetSourceProjectiveMap R ι X C p j f = p ≫ j ≫ f := by
  simp [fixedTargetSourceProjectiveMap]

/-- The original source open and its entire infinity complement are disjoint. -/
theorem source_disjoint_infinity :
    Disjoint (Set.range (inclusion C (p ≫ j)))
      (Set.range (infinityInclusion C (p ≫ j))) := by
  rw [range_infinityInclusion]
  exact disjoint_compl_right

/-- The retained punctured target is the original overlap, never a new parameter shrink. -/
theorem fixedTarget_retained_cover (a : A ⟶ X) (z : Z ⟶ X) (s : Z ⟶ Y)
    (H : IsPullback s (𝟙 Z) p z)
    (hcover : ∀ x : X, x ∈ Set.range a ∨ x ∈ Set.range z)
    (c : (genericMap C (p ≫ j)).normalization) :
    c ∈ Set.range (pullback.fst p a ≫ inclusion C (p ≫ j)) ∨
      c ∈ Set.range (infinityInclusion C (p ≫ j)) ∨
      c ∈ Set.range (s ≫ inclusion C (p ≫ j)) := by
  by_cases hc : c ∈ Set.range (inclusion C (p ≫ j))
  · obtain ⟨y, rfl⟩ := hc
    rcases hcover (p y) with ⟨b, hb⟩ | ⟨b, hb⟩
    · obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
        (IsPullback.of_hasPullback p a) y b hb.symm
      exact Or.inl ⟨w, by simp only [Scheme.Hom.comp_apply, hw]⟩
    · obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback H y b hb.symm
      exact Or.inr (Or.inr ⟨w, by simp only [Scheme.Hom.comp_apply, hw]⟩)
  · exact Or.inr (Or.inl (by rwa [range_infinityInclusion]))

omit [IsLocallyNoetherian C] [IsSeparated p] [IsFinite f] in
/-- Literal structural-map comparison, including the unchanged curve base. -/
@[reassoc]
theorem fixedTargetSource_over (q : X ⟶ Spec (.of R))
    (hq : j ≫ (f ≫ toSpec R ι) = q) :
    inclusion C (p ≫ j) ≫
      (fixedTargetSourceProjectiveMap R ι X C p j f ≫ toSpec R ι) = p ≫ q := by
  simp only [fixedTargetSourceProjectiveMap, ← Category.assoc, inclusion_over]
  simpa only [Category.assoc] using congrArg (p ≫ ·) hq

omit [IsLocallyNoetherian C] [IsSeparated p] [IsFinite f] in
/-- Smoothness is used only on the original retained source, never on its normalization. -/
theorem fixedTargetSource_smooth (q : X ⟶ Spec (.of R))
    [SmoothOfRelativeDimension 1 q] (hq : j ≫ (f ≫ toSpec R ι) = q) :
    SmoothOfRelativeDimension 1 (inclusion C (p ≫ j) ≫
      (fixedTargetSourceProjectiveMap R ι X C p j f ≫ toSpec R ι)) := by
  rw [fixedTargetSource_over R ι X C p j f q hq]
  exact smoothOfRelativeDimension_comp (n := 0) (m := 1) _ _

omit [IsLocallyNoetherian C] [IsSeparated p] [IsFinite f] in
/-- The entire original overlap remains a smooth relative curve. -/
theorem fixedTargetRetained_smooth (q : X ⟶ Spec (.of R))
    [SmoothOfRelativeDimension 1 q] (hq : j ≫ (f ≫ toSpec R ι) = q)
    (a : A ⟶ X) [IsOpenImmersion a] :
    SmoothOfRelativeDimension 1 ((pullback.fst p a ≫ inclusion C (p ≫ j)) ≫
      (fixedTargetSourceProjectiveMap R ι X C p j f ≫ toSpec R ι)) := by
  rw [Category.assoc, fixedTargetSource_over R ι X C p j f q hq]
  have : SmoothOfRelativeDimension 1 (p ≫ q) :=
    smoothOfRelativeDimension_comp (n := 0) (m := 1) _ _
  exact smoothOfRelativeDimension_comp (n := 0) (m := 1) _ _
end AlgebraicGeometry.Scheme.EtaleCompactification
