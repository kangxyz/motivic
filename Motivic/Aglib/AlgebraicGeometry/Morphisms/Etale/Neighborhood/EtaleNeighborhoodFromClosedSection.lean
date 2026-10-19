/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.FiniteEtaleNeighborhoodIso
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# An étale neighborhood from a section on a closed subscheme

A section of an étale map over a closed subscheme has open image there.
Removing the complementary closed subset from the original étale source gives
an actual open refinement which is an isomorphism over the closed subscheme.
The closed subscheme need not be reduced or finite.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

set_option backward.isDefEq.respectTransparency false in
/-- A section over a closed subscheme extends to an actual étale neighborhood
which is isomorphic over that subscheme, by removing the unwanted branches. -/
theorem exists_open_iso_over_closed_of_section
    {Y X Z : Scheme.{u}} (p : Y ⟶ X) [Etale p]
    (z : Z ⟶ X) [IsClosedImmersion z]
    (s : Z ⟶ pullback p z) (hs : s ≫ pullback.snd p z = 𝟙 Z) :
    ∃ W : Y.Opens, IsIso (pullback.snd (W.ι ≫ p) z) := by
  have : IsOpenImmersion s := isOpenImmersion_of_section_of_etale _ s hs
  let B : Set Y := pullback.fst p z '' (Set.range s)ᶜ
  have hB : IsClosed B :=
    (pullback.fst p z).isClosedEmbedding.isClosedMap _ s.isOpenEmbedding.isOpen_range.isClosed_compl
  let W : Y.Opens := ⟨Bᶜ, hB.isOpen_compl⟩
  have hW (t : (pullback p z : Scheme)) : pullback.fst p z t ∈ W ↔ t ∈ Set.range s := by
    change pullback.fst p z t ∉ B ↔ t ∈ Set.range s
    simp only [B, Set.mem_image, Set.mem_compl_iff]
    constructor
    · intro ht
      by_contra hn
      exact ht ⟨t, hn, rfl⟩
    · rintro ⟨v, rfl⟩ ⟨t, ht, he⟩
      exact ht ⟨v, (pullback.fst p z).isClosedEmbedding.injective he |>.symm⟩
  have hrange : Set.range (s ≫ pullback.fst p z) ⊆ Set.range W.ι := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (hW (s v)).mpr ⟨v, rfl⟩
  let a : Z ⟶ W.toScheme := IsOpenImmersion.lift W.ι (s ≫ pullback.fst p z) hrange
  have ha : a ≫ W.ι = s ≫ pullback.fst p z := IsOpenImmersion.lift_fac _ _ _
  have hap : a ≫ (W.ι ≫ p) = z := by
    rw [← Category.assoc, ha, Category.assoc, pullback.condition,
      ← Category.assoc, hs, Category.id_comp]
  let t : Z ⟶ pullback (W.ι ≫ p) z := pullback.lift a (𝟙 Z) (by simpa using hap)
  have ht : t ≫ pullback.snd (W.ι ≫ p) z = 𝟙 Z := pullback.lift_snd _ _ _
  have : IsOpenImmersion t := isOpenImmersion_of_section_of_etale _ t ht
  let b : pullback (W.ι ≫ p) z ⟶ pullback p z :=
    pullback.map _ _ _ _ W.ι (𝟙 Z) (𝟙 X) (by simp) (by simp)
  have hb₁ : b ≫ pullback.fst p z = pullback.fst (W.ι ≫ p) z ≫ W.ι := by simp [b]
  have hb₂ : b ≫ pullback.snd p z = pullback.snd (W.ι ≫ p) z := by simp [b]
  have : Surjective t := ⟨fun v ↦ by
    have hbW : pullback.fst p z (b v) ∈ W := by
      rw [← Scheme.Hom.comp_apply, hb₁]
      exact (pullback.fst (W.ι ≫ p) z v).property
    obtain ⟨v₀, hv₀⟩ := (hW (b v)).mp hbW
    refine ⟨v₀, ?_⟩
    apply (pullback.fst (W.ι ≫ p) z).isClosedEmbedding.injective
    apply W.ι.isOpenEmbedding.injective
    have he : W.ι (a v₀) = pullback.fst p z (s v₀) :=
      congrArg (fun f : Z ⟶ Y ↦ f v₀) ha
    change W.ι ((t ≫ pullback.fst (W.ι ≫ p) z) v₀) = _
    rw [show t ≫ pullback.fst (W.ι ≫ p) z = a from pullback.lift_fst _ _ _, he, hv₀]
    exact congrArg (fun f : pullback (W.ι ≫ p) z ⟶ Y ↦ f v) hb₁⟩
  have : IsIso t := (isIso_iff_isOpenImmersion_and_surjective t).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso (t ≫ pullback.snd (W.ι ≫ p) z) := by rw [ht]; infer_instance
  exact ⟨W, IsIso.of_isIso_comp_left t _⟩

end AlgebraicGeometry.Scheme.Hom
