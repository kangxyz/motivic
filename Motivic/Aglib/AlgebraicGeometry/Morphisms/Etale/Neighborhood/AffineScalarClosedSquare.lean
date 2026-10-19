/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.EtaleComparison.AffinePrincipalDivisorChart
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.OriginalEtaleMap

/-! # Original affine étale diagrams under scalar base change

The literal mapped ideal defines the whole scalar closed scheme. The good
finite chart and original closed section are transported through actual
Cartesian squares, without replacing the quotient by its reduction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (B S : Type u) [CommRing B] [CommRing S] [Algebra B S]

/-- The original good open becomes the complement of the literal mapped ideal. -/
theorem spec_preimage_complement_zeroLocus_map
    (I : Ideal B) (U : (Spec (.of B)).Opens)
    (hU : (U : Set (Spec (.of B))) = (PrimeSpectrum.zeroLocus (I : Set B))ᶜ) :
    ((Spec.map (CommRingCat.ofHom (algebraMap B S)) ⁻¹ᵁ U) :
      Set (Spec (.of S))) =
        (PrimeSpectrum.zeroLocus (I.map (algebraMap B S) : Set S))ᶜ := by
  ext x
  change Spec.map (CommRingCat.ofHom (algebraMap B S)) x ∈ (U : Set _) ↔ _
  rw [hU]
  change ¬ I ≤ Ideal.comap (algebraMap B S) x.asIdeal ↔
    ¬ I.map (algebraMap B S) ≤ x.asIdeal
  rw [Ideal.map_le_iff_le_comap]

/-- Finiteness on the original good chart survives with the exact mapped bad ideal. -/
theorem finite_pullback_on_mapped_ideal_complement
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of B))
    (I : Ideal B) (U : (Spec (.of B)).Opens)
    (hU : (U : Set (Spec (.of B))) = (PrimeSpectrum.zeroLocus (I : Set B))ᶜ)
    [IsFinite (p ∣_ U)] :
    ((Spec.map (CommRingCat.ofHom (algebraMap B S)) ⁻¹ᵁ U) :
      Set (Spec (.of S))) =
        (PrimeSpectrum.zeroLocus (I.map (algebraMap B S) : Set S))ᶜ ∧
    IsFinite ((pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap B S)))) ∣_
      (Spec.map (CommRingCat.ofHom (algebraMap B S)) ⁻¹ᵁ U)) :=
  ⟨spec_preimage_complement_zeroLocus_map B S I U hU,
    finite_pullback_on_original_chart p _ U⟩

/-- The full mapped quotient has exactly the inverse image of the original support. -/
theorem range_spec_quotient_map_baseChange (J : Ideal B) :
    Set.range (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (J.map (algebraMap B S))))) =
      (Spec.map (CommRingCat.ofHom (algebraMap B S))) ⁻¹'
        Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) := by
  have hB : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) =
      PrimeSpectrum.zeroLocus (J : Set B) := by
    simpa only [Ideal.mk_ker] using
      range_comap_of_surjective (B ⧸ J) (Ideal.Quotient.mk J)
        Ideal.Quotient.mk_surjective
  have hS : Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (J.map (algebraMap B S)))) =
      PrimeSpectrum.zeroLocus (J.map (algebraMap B S) : Set S) := by
    simpa only [Ideal.mk_ker] using
      range_comap_of_surjective (S ⧸ J.map (algebraMap B S))
        (Ideal.Quotient.mk (J.map (algebraMap B S))) Ideal.Quotient.mk_surjective
  change Set.range (PrimeSpectrum.comap
    (Ideal.Quotient.mk (J.map (algebraMap B S)))) =
    (PrimeSpectrum.comap (algebraMap B S)) ⁻¹'
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J))
  rw [hB, hS, PrimeSpectrum.preimage_comap_zeroLocus]
  exact PrimeSpectrum.zeroLocus_span _

variable (J : Ideal B) {Y : Scheme.{u}} (p : Y ⟶ Spec (.of B))
  (s : Spec (.of (B ⧸ J)) ⟶ Y)
  (hs : s ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))

/-- The unchanged original section lifted to the actual scalar étale pullback. -/
def quotientBaseChangeEtaleLift :
    Spec (.of (S ⧸ J.map (algebraMap B S))) ⟶
      pullback p (Spec.map (CommRingCat.ofHom (algebraMap B S))) :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (J.map (algebraMap B S))
      (algebraMap B S) Ideal.le_comap_map)) ≫ s)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap B S)))))
    (by
      rw [Category.assoc, hs]
      exact (isPullback_Spec_quotient_map B S J).w.symm)

@[reassoc (attr := simp)]
theorem quotientBaseChangeEtaleLift_fst :
    quotientBaseChangeEtaleLift B S J p s hs ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (J.map (algebraMap B S))
        (algebraMap B S) Ideal.le_comap_map)) ≫ s :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem quotientBaseChangeEtaleLift_snd :
    quotientBaseChangeEtaleLift B S J p s hs ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap B S)))) :=
  pullback.lift_snd _ _ _

/-- The original whole closed Cartesian square survives scalar base change. -/
theorem quotientBaseChangeEtaleLift_isPullback
    (H : IsPullback s (𝟙 _) p
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) :
    IsPullback (quotientBaseChangeEtaleLift B S J p s hs) (𝟙 _)
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap B S))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap B S))))) := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.quotientMap (J.map (algebraMap B S))
    (algebraMap B S) Ideal.le_comap_map))
  have Hbig := (IsPullback.of_id_snd (f := q)).paste_horiz H
  rw [← (isPullback_Spec_quotient_map B S J).w] at Hbig
  apply IsPullback.of_right
    (h₁₂ := pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap B S))))
    ?_ ?_ (IsPullback.of_hasPullback _ _)
  · simpa only [quotientBaseChangeEtaleLift_fst] using Hbig
  · simp only [quotientBaseChangeEtaleLift_snd, Category.id_comp]

/-- The original puncture and full scalar closed scheme remain disjoint. -/
theorem quotientBaseChange_punctured_disjoint
    {A : Scheme.{u}} (a : A ⟶ Spec (.of B)) [IsOpenImmersion a]
    (ha : Disjoint (Set.range a)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))) :
    Disjoint
      (Set.range (pullback.snd a (Spec.map (CommRingCat.ofHom (algebraMap B S)))))
      (Set.range (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (J.map (algebraMap B S)))))) := by
  rw [IsOpenImmersion.range_pullbackSnd, range_spec_quotient_map_baseChange B S J]
  exact Disjoint.preimage _ ha

/-- The actual scalar target is covered by the original puncture and mapped quotient. -/
theorem quotientBaseChange_punctured_cover
    {A : Scheme.{u}} (a : A ⟶ Spec (.of B)) [IsOpenImmersion a]
    (hcover : ∀ x : Spec (.of B), x ∈ Set.range a ∨
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) :
    ∀ x : Spec (.of S),
      x ∈ Set.range (pullback.snd a
        (Spec.map (CommRingCat.ofHom (algebraMap B S)))) ∨
      x ∈ Set.range (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (J.map (algebraMap B S))))) := by
  intro x
  rw [IsOpenImmersion.range_pullbackSnd, range_spec_quotient_map_baseChange B S J]
  exact hcover (Spec.map (CommRingCat.ofHom (algebraMap B S)) x)

end AlgebraicGeometry.Scheme
