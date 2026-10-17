module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.FiniteEnvelopeGoodOpen
public import Motivic.Aglib.AlgebraicGeometry.Normalization.FiniteBoundarySourceLift
/-! # The original finite chart inside a fixed compact target -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme
variable {Y X C : Scheme.{u}} (p : Y ⟶ X) (j : X ⟶ C) [IsOpenImmersion j]
  (U : X.Opens)

/-- An open embedding is an isomorphism above the image of any original open. -/
theorem isIso_restrict_open_image : IsIso (j ∣_ j ''ᵁ U) := by
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨inferInstance, ⟨fun x => ?_⟩⟩
  obtain ⟨y, hy, he⟩ := x.property
  have hmem : y ∈ j ⁻¹ᵁ (j ''ᵁ U) := ⟨y, hy, rfl⟩
  refine ⟨⟨y, hmem⟩, ?_⟩
  apply Subtype.ext
  exact (morphismRestrict_base_coe j _ ⟨y, hmem⟩).trans he

/-- Finiteness of the original chart survives its actual embedding in the compact target. -/
theorem finite_comp_restrict_open_image [IsFinite (p ∣_ U)] :
    IsFinite ((p ≫ j) ∣_ j ''ᵁ U) := by
  have : IsIso (j ∣_ j ''ᵁ U) := isIso_restrict_open_image j U
  have h : IsFinite (p ∣_ j ⁻¹ᵁ (j ''ᵁ U)) := by
    rw [j.preimage_image_eq]
    infer_instance
  rw [morphismRestrict_comp]
  infer_instance

/-- The literal Cartesian chart used by normalization is finite as well. -/
theorem finite_comp_pullback_open_image [IsFinite (p ∣_ U)] :
    IsFinite (pullback.snd (p ≫ j) (j ''ᵁ U).ι) := by
  have := finite_comp_restrict_open_image p j U
  rw [← (isPullback_morphismRestrict (p ≫ j) (j ''ᵁ U)).flip.isoPullback_inv_snd]
  infer_instance
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.EtaleCompactification
variable (X C : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  [IsIntegral C] [IsLocallyNoetherian C]
  [∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x)]
  {Y S D : Scheme.{u}} (p : Y ⟶ X) [Etale p] [QuasiCompact p] [IsSeparated p]
  (j : X ⟶ C) [IsOpenImmersion j] [QuasiCompact j]
  (q : C ⟶ S) [IsProper q] (d : D ⟶ C) [IsFinite (d ≫ q)]

/-- One target presentation controls the entire source boundary. The good locus is
computed from the original étale map before choosing the target curve projection.
No separate source projection or source-boundary finiteness is assumed. -/
theorem finite_source_infinity_over_fixed_target
    (hbad : (j ''ᵁ finiteLocusOpen X p : Set C)ᶜ ⊆ Set.range d) :
    IsFinite (infinityInclusion C (p ≫ j) ≫
      (genericMap C (p ≫ j)).fromNormalization ≫ q) := by
  have := finite_on_finiteLocusOpen X p
  have := finite_comp_pullback_open_image p j (finiteLocusOpen X p)
  exact finite_infinity_of_finite_target_boundary C (p ≫ j) q d
    (j ''ᵁ finiteLocusOpen X p) hbad
/-- The entire source boundary, including the original possibly nonreduced closed
boundary, is finite over the unchanged base. -/
theorem finite_full_source_boundary_over_fixed_target
    (hbad : (j ''ᵁ finiteLocusOpen X p : Set C)ᶜ ⊆ Set.range d)
    {Z : Scheme.{u}} (s : Z ⟶ Y) [IsFinite (s ≫ p ≫ j ≫ q)] :
    IsFinite (boundaryInclusion C (p ≫ j) s ≫
      (genericMap C (p ≫ j)).fromNormalization ≫ q) := by
  have := finite_source_infinity_over_fixed_target X C p j q d hbad
  have : IsFinite ((s ≫ inclusion C (p ≫ j)) ≫
      (genericMap C (p ≫ j)).fromNormalization ≫ q) := by
    simpa only [Category.assoc, reassoc_of% (inclusion_over C (p ≫ j))] using
      (inferInstance : IsFinite (s ≫ p ≫ j ≫ q))
  change IsFinite (coprod.desc _ _ ≫ _)
  rw [coprod.desc_comp]
  infer_instance

omit [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] in
/-- Closedness also concerns the original full coproduct, not its reduction. -/
theorem full_source_boundary_closed_over_fixed_target
    {Z : Scheme.{u}} (s : Z ⟶ Y) [IsClosedImmersion s]
    [IsFinite (s ≫ p ≫ j ≫ q)] :
    IsClosedImmersion (boundaryInclusion C (p ≫ j) s) := by
  have : IsProper (s ≫ (p ≫ j) ≫ q) := by
    simpa only [Category.assoc] using
      (inferInstance : IsProper (s ≫ p ≫ j ≫ q))
  exact boundaryInclusion_isClosedImmersion C (p ≫ j) s q
end AlgebraicGeometry.Scheme.EtaleCompactification
