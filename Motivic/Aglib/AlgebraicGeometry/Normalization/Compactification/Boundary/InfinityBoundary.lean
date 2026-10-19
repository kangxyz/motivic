/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Etale
public import Mathlib.Topology.KrullDimension

/-! # The actual full infinity boundary of the constructed étale compactification -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
attribute [local instance] specializationOrder
universe u
namespace AlgebraicGeometry.Scheme.EtaleCompactification
variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] [QuasiCompact f] [IsSeparated f]

omit [IsLocallyNoetherian X] [IsSeparated f] in
/-- Every point over the generic point already belongs to the original étale open. -/
theorem generic_fibre_mem_inclusion (x : (genericMap X f).normalization)
    (hx : (genericMap X f).fromNormalization x = genericPoint X) :
    x ∈ Set.range (inclusion X f) := by
  let H := Scheme.FiniteEtale.GenericNormalization.isPullback_generic X (genericCover X f)
  obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback H x
    (IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)))
    (by simpa only [Scheme.fromSpecStalk_closedPoint] using hx)
  refine ⟨pullback.snd (X.fromSpecStalk (genericPoint X)) f w, ?_⟩
  change (pullback.snd (X.fromSpecStalk (genericPoint X)) f ≫ inclusion X f) w = x
  rw [generic_inclusion]
  exact hw

/-- The ideal of the entire complement of the original source open. -/
def infinityIdeal : ((genericMap X f).normalization).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨(Set.range (inclusion X f))ᶜ, (inclusion X f).isOpenEmbedding.isOpen_range.isClosed_compl⟩

/-- The actual reduced closed complement; no subset of boundary points is selected. -/
def infinity : Scheme.{u} := (infinityIdeal X f).subscheme

/-- Original closed boundary inclusion. -/
def infinityInclusion : infinity X f ⟶ (genericMap X f).normalization :=
  (infinityIdeal X f).subschemeι

instance : IsClosedImmersion (infinityInclusion X f) := by
  dsimp [infinityInclusion]
  infer_instance

/-- The range is exactly the whole missing open complement. -/
theorem range_infinityInclusion : Set.range (infinityInclusion X f) =
    (Set.range (inclusion X f))ᶜ := by
  change Set.range (infinityIdeal X f).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι]
  simp [infinityIdeal]

/-- The full boundary, not just a chosen subset, avoids the generic base point. -/
theorem infinity_avoids_generic (x : infinity X f) :
    (infinityInclusion X f ≫ (genericMap X f).fromNormalization) x ≠ genericPoint X := by
  intro hx
  have hn : infinityInclusion X f x ∉ Set.range (inclusion X f) := by
    rw [← Set.mem_compl_iff, ← range_infinityInclusion]
    exact ⟨x, rfl⟩
  exact hn (generic_fibre_mem_inclusion X f _ hx)


/-- The full infinity boundary has finitely many points on a Noetherian integral curve.
The dimension hypothesis concerns the base curve, not the constructed boundary. -/
theorem finite_infinity [CompactSpace X]
    (hcurve : ∀ x : X, x ≠ genericPoint X → Order.coheight x = 1) :
    Finite (infinity X f) := by
  have : IsNoetherian X := ⟨⟩
  let q := infinityInclusion X f ≫ (genericMap X f).fromNormalization
  have : IsFinite q := by dsimp [q]; infer_instance
  let P : Set X := Set.range q
  have hP : IsClosed P := by
    simpa [P, ← Set.image_univ] using q.isClosedMap _ isClosed_univ
  have hη : genericPoint X ∉ P := by
    rintro ⟨x, hx⟩
    exact infinity_avoids_generic X f x hx
  have : QuasiSober P := hP.isClosedEmbedding_subtypeVal.quasiSober
  have hn : closure P ≠ Set.univ := by
    rw [hP.closure_eq]
    intro he
    exact hη (he.symm ▸ Set.mem_univ _)
  have hpfin : P.Finite :=
    (TopologicalSpace.NoetherianSpace.finite_coheight_one_of_closure_ne_univ hn).subset
      (fun x hx => ⟨hx, hcurve x (fun he => hη (he ▸ hx))⟩)
  have hall : (Set.univ : Set (infinity X f)).Finite := by
    simpa [P] using q.finite_preimage hpfin
  exact Set.finite_univ_iff.mp hall

/-- Properness and the derived finite underlying boundary imply actual scheme finiteness. -/
theorem finite_infinity_projection [CompactSpace X]
    (hcurve : ∀ x : X, x ≠ genericPoint X → Order.coheight x = 1)
    {S : Scheme.{u}} (p : X ⟶ S) [IsProper p] :
    IsFinite (infinityInclusion X f ≫ (genericMap X f).fromNormalization ≫ p) := by
  let := finite_infinity X f hcurve
  let q := infinityInclusion X f ≫ (genericMap X f).fromNormalization ≫ p
  have : IsProper q := by dsimp [q]; infer_instance
  have : LocallyQuasiFinite q := LocallyQuasiFinite.of_finite_preimage_singleton q
    (fun _ => Set.toFinite _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite q

end AlgebraicGeometry.Scheme.EtaleCompactification
