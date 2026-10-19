/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.FiniteSourceBoundaryAffineNeighborhood

/-! # Actual source and target boundary ambients before choosing sections

Two localizations of the original coefficient base produce the source and target
ambients. The second step preserves the first source ambient by affine base change.
The target uses its own full boundary, not the image of the source boundary.
No parameter open or new section is chosen.


Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.SourceTargetBoundaryAffineNeighborhood`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.ProjectiveSpace

/-- Actual affine source and target ambients containing their original full
boundaries after two coefficient-only localizations. All displayed schemes and
maps are the literal successive pullbacks of the original finite cover. -/
theorem exists_source_target_affine_boundary_ambients
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C B Z : Scheme.{u}} (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]
    (b : B ⟶ C) [IsFinite ((b ≫ f) ≫ toSpec R ι)]
    (z : Z ⟶ ProjectiveSpace R ι) [IsFinite (z ≫ toSpec R ι)] :
    ∃ r : R, r ≠ 0 ∧
      let S := Localization.Away r
      let m₁ := ProjectiveSpace.map (algebraMap R S) ι
      let f₁ := pullback.snd f m₁
      let b₁ : pullback (b ≫ f) m₁ ⟶ pullback f m₁ := pullback.lift (pullback.fst (b ≫ f) m₁ ≫ b)
        (pullback.snd (b ≫ f) m₁) (by simp [Category.assoc, pullback.condition])
      let z₁ := pullback.snd z m₁
      ∃ s : S, s ≠ 0 ∧
        let m₂ := ProjectiveSpace.map (algebraMap S (Localization.Away s)) ι
        let t₂ := pullback.fst (𝟙 (ProjectiveSpace S ι)) m₂
        let c₂ := pullback.fst f₁ t₂
        let z₂ := pullback.lift (pullback.fst (z₁ ≫ 𝟙 _) m₂ ≫ z₁)
          (pullback.snd (z₁ ≫ 𝟙 _) m₂) (by
            simpa only [Category.assoc, Category.comp_id] using
              (pullback.condition (f := z₁ ≫ 𝟙 _) (g := m₂)))
        ∃ U : (pullback f₁ t₂).Opens,
          ∃ V : (pullback (𝟙 (ProjectiveSpace S ι)) m₂).Opens,
            IsAffineOpen U ∧ IsAffineOpen V ∧
            (∃ u : pullback b₁ c₂ ⟶ U.toScheme,
              u ≫ U.ι = pullback.snd b₁ c₂) ∧
            (∃ v : pullback (z₁ ≫ 𝟙 _) m₂ ⟶ V.toScheme, v ≫ V.ι = z₂) := by
  obtain ⟨r, hr, W, hW, t, ht⟩ :=
    exists_affine_full_boundary_coefficient_neighborhood R ι n e f b
  refine ⟨r, hr, ?_⟩
  let S := Localization.Away r
  let : IsDomain S := Localization.Away.isDomain hr
  let m₁ := ProjectiveSpace.map (algebraMap R S) ι
  let f₁ := pullback.snd f m₁
  let b₁ : pullback (b ≫ f) m₁ ⟶ pullback f m₁ := pullback.lift (pullback.fst (b ≫ f) m₁ ≫ b)
    (pullback.snd (b ≫ f) m₁) (by simp [Category.assoc, pullback.condition])
  let z₁ := pullback.snd z m₁
  have H : IsPullback (pullback.fst z m₁) (z₁ ≫ toSpec S ι)
      (z ≫ toSpec R ι) (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    (IsPullback.of_hasPullback z m₁).paste_vert (isPullback_map (algebraMap R S) ι)
  have : IsFinite (z₁ ≫ toSpec S ι) := MorphismProperty.of_isPullback H inferInstance
  have : IsFinite ((z₁ ≫ 𝟙 _) ≫ toSpec S ι) := by simpa using this
  obtain ⟨s, hs, V, hV, v, hv⟩ :=
    exists_affine_full_boundary_coefficient_neighborhood S ι n e (𝟙 _) z₁
  refine ⟨s, hs, ?_⟩
  let m₂ := ProjectiveSpace.map (algebraMap S (Localization.Away s)) ι
  let t₂ := pullback.fst (𝟙 (ProjectiveSpace S ι)) m₂
  let c₂ := pullback.fst f₁ t₂
  have : IsAffineHom m₂ :=
    MorphismProperty.of_isPullback
      (isPullback_map (algebraMap S (Localization.Away s)) ι).flip inferInstance
  have : IsAffineHom t₂ :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (𝟙 (ProjectiveSpace S ι)) m₂).flip inferInstance
  have : IsAffineHom c₂ :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f₁ t₂).flip inferInstance
  let U := c₂ ⁻¹ᵁ W
  have hU : IsAffineOpen U := hW.preimage c₂
  have hbU : Set.range (pullback.snd b₁ c₂) ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change c₂ (pullback.snd b₁ c₂ x) ∈ W
    have hx := congrArg (fun k => k x) (pullback.condition (f := b₁) (g := c₂))
    change b₁ (pullback.fst b₁ c₂ x) = c₂ (pullback.snd b₁ c₂ x) at hx
    rw [← hx]
    have ht' : t ≫ W.ι = b₁ := ht
    have hy := congrArg (fun k => k (pullback.fst b₁ c₂ x)) ht'
    exact hy ▸ (t (pullback.fst b₁ c₂ x)).property
  refine ⟨U, V, hU, hV, ?_, v, hv⟩
  exact ⟨IsOpenImmersion.lift U.ι (pullback.snd b₁ c₂) hbU,
    IsOpenImmersion.lift_fac _ _ _⟩

end AlgebraicGeometry.ProjectiveSpace
