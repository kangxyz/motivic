/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.EtaleComparison.SmoothAffinePresentation
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.Fibers.AffinePresentation
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.EtaleComparison.AffinePrincipalDivisorChart
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.EtaleComparison.OriginalDivisorNeighborhoodOverBase
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.EtaleComparison.AffineDivisorEtaleComparisonOverBase

/-! # Actual local étale cylinder comparison for a smooth Cartier pair -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme

/-- Every point of a smooth Cartier divisor admits an affine neighborhood whose
original closed restriction has a common étale neighborhood with its own literal
zero-section cylinder. No chart, retraction, or residue-field condition is assumed. -/
theorem exists_smooth_cartier_etale_cylinder_comparison_over_base
    {k : Type u} [Field k] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (p : X ⟶ Spec (.of k))
    [Smooth p] [Smooth (i ≫ p)]
    (hI : IsLocallyRankOne X (Scheme.Hom.idealModule i)) (z : Z) :
    ∃ U : X.Opens, IsAffineOpen U ∧ i z ∈ U ∧
      ∃ (V : Scheme.{u}) (a : V ⟶ U.toScheme)
        (b : V ⟶ Scheme.Hom.cylinder k ((i ⁻¹ᵁ U).ι ≫ i ≫ p))
        (j : (i ⁻¹ᵁ U).toScheme ⟶ V),
        Etale a ∧ Etale b ∧
        IsPullback j (𝟙 _) a (i ∣_ U) ∧
        IsPullback j (𝟙 _) b
          (Scheme.Hom.cylinderZeroSection k ((i ⁻¹ᵁ U).ι ≫ i ≫ p)) ∧
        IsIso (pullback.snd a (i ∣_ U)) ∧
        IsIso (pullback.snd b
          (Scheme.Hom.cylinderZeroSection k ((i ⁻¹ᵁ U).ι ≫ i ≫ p))) ∧
        a ≫ U.ι ≫ p = b ≫ pullback.snd _ _ ≫ (i ⁻¹ᵁ U).ι ≫ i ≫ p ∧
        IsSeparated a ∧ IsSeparated b ∧ QuasiCompact a ∧ QuasiCompact b := by
  obtain ⟨U, hU, hz, t, _, _, ht, hker, _, _, htp⟩ :=
    exists_smooth_affine_cartier_presentation i p hI z
  let R := Γ(X, U)
  let φ : k →+* R := (Spec.preimage (hU.fromSpec ≫ p)).hom
  have hφSpec : Spec.map (CommRingCat.ofHom φ) = hU.fromSpec ≫ p := by
    exact Spec.map_preimage _
  have hφ : φ.Smooth := by
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mp
    rw [Spec.map_preimage]
    infer_instance
  have hφZ : ((i.app U).hom.comp φ).Smooth := by
    change (CommRingCat.ofHom φ ≫ i.app U).hom.Smooth
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mp
    rw [Spec.map_comp, hφSpec, ← Category.assoc]
    rw [show Spec.map (i.app U) ≫ hU.fromSpec = (hU.preimage i).fromSpec ≫ i from by
      simpa only [Scheme.Hom.app_eq_appLE] using
        IsAffineOpen.SpecMap_appLE_fromSpec i hU (hU.preimage i) le_rfl]
    rw [Category.assoc]
    infer_instance
  let : Algebra k R := φ.toAlgebra
  have : Algebra.Smooth k R := hφ
  have : Algebra.FormallySmooth k (R ⧸ Ideal.span {t}) :=
    formallySmooth_principal_quotient_of_surjective (i.app U).hom
      (i.app_surjective U hU) t hker hφZ
  obtain ⟨r, hr, V, a, b, j, ha, hb, hpa, hpb, hbase, hsa, hsb, hqa, hqb⟩ :=
    exists_etale_comparison_with_divisor_cylinder_over_base k R t ht
      (hU.primeIdealOf ⟨i z, hz⟩).asIdeal htp
  let B := Localization.Away r
  let D := B ⧸ Ideal.span {algebraMap R B t}
  let u : Spec (.of B) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ hU.fromSpec
  have hu : IsOpenImmersion u := inferInstance
  have hzu : i z ∈ Set.range u := by
    obtain ⟨w, hw⟩ : hU.primeIdealOf ⟨i z, hz⟩ ∈
        Set.range (PrimeSpectrum.comap (algebraMap R B)) := by
      rw [PrimeSpectrum.localization_away_comap_range B r]
      exact hr
    refine ⟨w, ?_⟩
    change hU.fromSpec (PrimeSpectrum.comap (algebraMap R B) w) = i z
    rw [hw, hU.fromSpec_primeIdealOf]
  obtain ⟨s, hs⟩ := i.exists_quotient_isPullback_of_kernel U hU (Ideal.span {t}) hker
  obtain ⟨s', hs'⟩ := exists_isPullback_Spec_quotient_of_map_eq (algebraMap R B)
    (Ideal.span {t}) (Ideal.span {algebraMap R B t})
    (by rw [Ideal.map_span, Set.image_singleton])
  have huBase : u ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
    dsimp only [u]
    rw [Category.assoc, ← hφSpec, ← Spec.map_comp]
    rfl
  have hOrig := hs'.paste_vert hs
  have hDBase : Spec.map (CommRingCat.ofHom (algebraMap k D)) = (s' ≫ s) ≫ i ≫ p := by
    rw [← hOrig.w_assoc, huBase, ← Spec.map_comp]
    rfl
  have hbase' : a ≫ u ≫ p = b ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : D →+* Polynomial D)) ≫
      (s' ≫ s) ≫ i ≫ p := by
    rw [huBase, ← hDBase, ← Spec.map_comp]
    exact hbase
  have : Etale a := ha
  have : Etale b := hb
  have : IsSeparated a := hsa
  have : IsSeparated b := hsb
  have : QuasiCompact a := hqa
  have : QuasiCompact b := hqb
  obtain ⟨W, hW, hzW, a', b', j', ha', hb', hpa', hpb', hbase'', hsa', hsb', hqa', hqb'⟩ :=
    exists_original_open_divisor_comparison_over_base i p u
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {algebraMap R B t})))) (s' ≫ s)
      hOrig z hzu a b j hpa hpb hbase'
  refine ⟨W, hW, hzW, V, a', b', j', ha', hb', hpa', hpb', ?_, ?_, hbase'', hsa', hsb', hqa', hqb'⟩
  · have : IsIso (hpa'.isoPullback.hom ≫ pullback.snd a' (i ∣_ W)) := by
      rw [hpa'.isoPullback_hom_snd]
      infer_instance
    exact IsIso.of_isIso_comp_left hpa'.isoPullback.hom _
  · have : IsIso (hpb'.isoPullback.hom ≫ pullback.snd b'
        (Scheme.Hom.cylinderZeroSection k ((i ⁻¹ᵁ W).ι ≫ i ≫ p))) := by
      rw [hpb'.isoPullback_hom_snd]
      infer_instance
    exact IsIso.of_isIso_comp_left hpb'.isoPullback.hom _

end AlgebraicGeometry.Scheme
