/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.InfinityBoundary
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
/-! # The original étale map is finite outside its actual missing-envelope image -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme
variable {Y E X : Scheme.{u}} (i : Y ⟶ E) [IsOpenImmersion i]
  (q : E ⟶ X) [IsFinite q]

/-- The complement of the closed image of the entire missing open source. -/
def finiteEnvelopeGoodOpen : X.Opens :=
  ⟨(q '' (Set.range i)ᶜ)ᶜ,
    (q.isClosedMap _ i.isOpenEmbedding.isOpen_range.isClosed_compl).isOpen_compl⟩

/-- No new envelope point remains above this actual target open. -/
theorem finiteEnvelopeGoodOpen_preimage_range :
    (q ⁻¹ᵁ finiteEnvelopeGoodOpen i q : Set E) ⊆ Set.range i := by
  intro x hx
  by_contra hn
  exact hx ⟨x, hn, rfl⟩

/-- The original restricted open immersion is genuinely an isomorphism, not only
an equality of supports. -/
theorem finiteEnvelopeGoodOpen_restrict_isIso :
    IsIso (i ∣_ q ⁻¹ᵁ finiteEnvelopeGoodOpen i q) := by
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨inferInstance, ⟨fun x => ?_⟩⟩
  obtain ⟨y, hy⟩ := finiteEnvelopeGoodOpen_preimage_range i q x.property
  have hmem : y ∈ i ⁻¹ᵁ (q ⁻¹ᵁ finiteEnvelopeGoodOpen i q) := by
    change i y ∈ q ⁻¹ᵁ finiteEnvelopeGoodOpen i q
    rw [hy]
    exact x.property
  refine ⟨⟨y, hmem⟩, ?_⟩
  apply Subtype.ext
  exact (morphismRestrict_base_coe i _ ⟨y, hmem⟩).trans hy

/-- Actual finiteness of the original map on the computed good target open. -/
theorem finiteEnvelopeGoodOpen_finite :
    IsFinite ((i ≫ q) ∣_ finiteEnvelopeGoodOpen i q) := by
  have hi := finiteEnvelopeGoodOpen_restrict_isIso i q
  have hq : IsFinite (q ∣_ finiteEnvelopeGoodOpen i q) :=
    MorphismProperty.of_isPullback
      (isPullback_morphismRestrict q (finiteEnvelopeGoodOpen i q)).flip inferInstance
  rw [morphismRestrict_comp]
  exact MorphismProperty.IsStableUnderComposition.comp_mem _ _
    (MorphismProperty.of_isIso @IsFinite _) hq

namespace EtaleCompactification
variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  {Y : Scheme.{u}} (p : Y ⟶ X) [Etale p] [QuasiCompact p] [IsSeparated p]

/-- This open is computed before any choice of relative curve projection. -/
def finiteLocusOpen : X.Opens :=
  finiteEnvelopeGoodOpen (inclusion X p) (genericMap X p).fromNormalization

/-- The exact original étale map is finite away from its fixed envelope bad image. -/
theorem finite_on_finiteLocusOpen : IsFinite (p ∣_ finiteLocusOpen X p) := by
  have h := finiteEnvelopeGoodOpen_finite (inclusion X p) (genericMap X p).fromNormalization
  change IsFinite ((inclusion X p ≫ (genericMap X p).fromNormalization) ∣_
    finiteLocusOpen X p) at h
  exact (congrArg (fun f : Y ⟶ X => IsFinite (f ∣_ finiteLocusOpen X p))
    (inclusion_over X p)).mp h
/-- The fixed bad image is proper: it does not contain the original generic point. -/
theorem genericPoint_mem_finiteLocusOpen : genericPoint X ∈ finiteLocusOpen X p := by
  rintro ⟨y, hy, he⟩
  exact hy (generic_fibre_mem_inclusion X p y he)
end EtaleCompactification
end AlgebraicGeometry.Scheme
