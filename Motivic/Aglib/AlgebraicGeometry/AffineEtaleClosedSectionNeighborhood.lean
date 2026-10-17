/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.AffineFiberPrincipalNeighborhood
public import Motivic.Aglib.AlgebraicGeometry.EtaleNeighborhoodFromClosedSection
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # A principal affine neighborhood of the original whole closed section

The closed scheme need not be reduced, finite, or Artinian. The original
section, not merely an unspecified new section, factors through the result.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme

/-- A closed subset of an affine scheme contained in an open has a single actual
principal neighborhood inside that open. No finiteness of its points is needed. -/
theorem exists_basicOpen_between_closed {Y : Scheme.{u}} [IsAffine Y]
    (C : Set Y) (hC : IsClosed C) (T : Y.Opens) (hCT : C ⊆ T) :
    ∃ r : Γ(Y, ⊤), C ⊆ Y.basicOpen r ∧ Y.basicOpen r ≤ T := by
  let U : TopologicalSpace.Opens (PrimeSpectrum Γ(Y, ⊤)) := Y.isoSpec.inv ⁻¹ᵁ T
  let C' := Y.isoSpec.inv ⁻¹' C
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal C').mp
    (hC.preimage Y.isoSpec.inv.continuous)
  have hJU : PrimeSpectrum.zeroLocus (J : Set Γ(Y, ⊤)) ⊆ (U : Set (PrimeSpectrum Γ(Y, ⊤))) := by
    rw [← hJ]
    exact fun _ hx => hCT hx
  obtain ⟨r, hr, hrU⟩ := PrimeSpectrum.exists_basicOpen_between_zeroLocus Γ(Y, ⊤) J U hJU
  have hJr : PrimeSpectrum.zeroLocus (J : Set Γ(Y, ⊤)) ⊆ PrimeSpectrum.basicOpen r := by
    intro x hx hxr
    have hone : (1 : Γ(Y, ⊤)) ∈ x.asIdeal := by
      convert x.asIdeal.sub_mem hxr (hx hr) using 1; ring
    exact x.asIdeal.one_notMem hone
  refine ⟨r, ?_, ?_⟩
  · rw [← Y.map_PrimeSpectrum_basicOpen_of_affine r]
    intro y hy
    apply hJr
    rw [← hJ]
    change Y.isoSpec.inv (Y.isoSpec.hom y) ∈ C
    simpa only [hom_inv_apply] using hy
  · rw [← Y.map_PrimeSpectrum_basicOpen_of_affine r]
    intro y hy
    have h := hrU hy
    change Y.isoSpec.inv (Y.isoSpec.hom y) ∈ T at h
    simpa only [hom_inv_apply] using h

namespace Hom

/-- A single principal open of the original affine etale source is an
isomorphism over the entire original closed subscheme and retains its specified
section scheme-theoretically. No reduction or shrinking of the closed scheme occurs. -/
theorem exists_basicOpen_iso_over_closed_of_section
    {Y X Z : Scheme.{u}} [IsAffine Y] (p : Y ⟶ X) [Etale p] [IsSeparated p]
    (z : Z ⟶ X) [IsClosedImmersion z]
    (s : Z ⟶ pullback p z) (hs : s ≫ pullback.snd p z = 𝟙 Z) :
    ∃ (r : Γ(Y, ⊤)) (a : Z ⟶ (Y.basicOpen r).toScheme),
      a ≫ (Y.basicOpen r).ι = s ≫ pullback.fst p z ∧
      IsAffineOpen (Y.basicOpen r) ∧
      IsIso (pullback.snd ((Y.basicOpen r).ι ≫ p) z) := by
  have : IsOpenImmersion s := isOpenImmersion_of_section_of_etale _ s hs
  let c := s ≫ pullback.fst p z
  have hc : c ≫ p = z := by
    dsimp only [c]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  have : IsClosedImmersion (c ≫ p) := by rw [hc]; infer_instance
  have : IsClosedImmersion c := IsClosedImmersion.of_comp c p
  let B : Set Y := pullback.fst p z '' (Set.range s)ᶜ
  have hB : IsClosed B := (pullback.fst p z).isClosedEmbedding.isClosedMap _
    s.isOpenEmbedding.isOpen_range.isClosed_compl
  let T : Y.Opens := ⟨Bᶜ, hB.isOpen_compl⟩
  have hT (t : (pullback p z : Scheme)) : pullback.fst p z t ∈ T ↔ t ∈ Set.range s := by
    change pullback.fst p z t ∉ B ↔ t ∈ Set.range s
    simp only [B, Set.mem_image, Set.mem_compl_iff]
    constructor
    · intro ht
      by_contra hn
      exact ht ⟨t, hn, rfl⟩
    · rintro ⟨v, rfl⟩ ⟨t, ht, he⟩
      exact ht ⟨v, (pullback.fst p z).isClosedEmbedding.injective he |>.symm⟩
  have hcT : Set.range c ⊆ T := by
    rintro _ ⟨v, rfl⟩
    exact (hT (s v)).mpr ⟨v, rfl⟩
  obtain ⟨r, hrC, hrT⟩ := exists_basicOpen_between_closed
    (Set.range c) c.isClosedEmbedding.isClosedMap.isClosed_range T hcT
  let W := Y.basicOpen r
  let a : Z ⟶ W.toScheme := IsOpenImmersion.lift W.ι c (by simpa using hrC)
  have ha : a ≫ W.ι = c := IsOpenImmersion.lift_fac _ _ _
  have hap : a ≫ (W.ι ≫ p) = z := by rw [← Category.assoc, ha, hc]
  let t : Z ⟶ pullback (W.ι ≫ p) z := pullback.lift a (𝟙 Z) (by simpa using hap)
  have ht : t ≫ pullback.snd (W.ι ≫ p) z = 𝟙 Z := pullback.lift_snd _ _ _
  have : IsOpenImmersion t := isOpenImmersion_of_section_of_etale _ t ht
  let b : pullback (W.ι ≫ p) z ⟶ pullback p z :=
    pullback.map _ _ _ _ W.ι (𝟙 Z) (𝟙 X) (by simp) (by simp)
  have hb₁ : b ≫ pullback.fst p z = pullback.fst (W.ι ≫ p) z ≫ W.ι := by simp [b]
  have : Surjective t := ⟨fun v => by
    have hbT : pullback.fst p z (b v) ∈ T := by
      rw [← Scheme.Hom.comp_apply, hb₁]
      exact hrT (pullback.fst (W.ι ≫ p) z v).property
    obtain ⟨v₀, hv₀⟩ := (hT (b v)).mp hbT
    refine ⟨v₀, ?_⟩
    apply (pullback.fst (W.ι ≫ p) z).isClosedEmbedding.injective
    apply W.ι.isOpenEmbedding.injective
    have he : W.ι (a v₀) = pullback.fst p z (s v₀) :=
      congrArg (fun f : Z ⟶ Y => f v₀) ha
    change W.ι ((t ≫ pullback.fst (W.ι ≫ p) z) v₀) = _
    rw [show t ≫ pullback.fst (W.ι ≫ p) z = a from pullback.lift_fst _ _ _, he, hv₀]
    exact congrArg (fun f : pullback (W.ι ≫ p) z ⟶ Y => f v) hb₁⟩
  have : IsIso t := (isIso_iff_isOpenImmersion_and_surjective t).mpr
    ⟨inferInstance, inferInstance⟩
  have : IsIso (t ≫ pullback.snd (W.ι ≫ p) z) := by rw [ht]; infer_instance
  exact ⟨r, a, ha, (isAffineOpen_top Y).basicOpen r,
    IsIso.of_isIso_comp_left t _⟩

end Hom
end AlgebraicGeometry.Scheme
