/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.Basic

/-! # Genuine missing infinity of a constructed target presentation

The finite full bad boundary is used only to bound fibres. It is never substituted
for the missing boundary, which is the actual closed complement of the target.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
variable {k : Type u} [Field k] {X Y A Z : Scheme.{u}}
  {b : X ⟶ Spec (.of k)} {p : Y ⟶ X} {a : A ⟶ X} {z : Z ⟶ X}
  {s : Z ⟶ Y} {x : X} (e : OriginalEtalePresentation k b p a z s x)
local instance missingBoundaryInclusionOpen : IsOpenImmersion e.inclusion := e.inclusion_open
local instance missingBoundaryProjectiveFinite : IsFinite e.projectiveMap := e.projective_finite
local instance missingBoundaryFullBoundaryFinite : IsFinite
    (e.boundaryInclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) := e.boundary_finite

/-- The actual missing closed scheme, distinct from the full bad boundary. -/
abbrev missing := retainedBoundary e.inclusion.opensRange
/-- The literal missing-boundary closed immersion. -/
abbrev missingInclusion : e.missing ⟶ e.compact :=
  retainedBoundaryInclusion e.inclusion.opensRange

/-- Its support is exactly the complement of the original target image. -/
theorem missing_range : Set.range e.missingInclusion = (Set.range e.inclusion)ᶜ := by
  simpa using range_retainedBoundaryInclusion e.inclusion.opensRange

/-- The genuine missing infinity is finite, derived from the constructed finite bad
boundary by properness and finite fibres, without replacing either closed scheme. -/
theorem missing_finite : IsFinite
    (e.missingInclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) := by
  let q := e.projectiveMap ≫ ProjectiveSpace.toSpec e.base (ULift.{u} (Fin 2))
  have : IsFinite (e.boundaryInclusion ≫ q) := e.boundary_finite
  have : IsProper q := by dsimp [q]; infer_instance
  have : IsProper (e.missingInclusion ≫ q) := inferInstance
  have hf : ∀ y, ((e.missingInclusion ≫ q) ⁻¹' {y}).Finite := by
    intro y
    have hD := ((e.boundaryInclusion ≫ q).finite_preimage_singleton y).image
      e.boundaryInclusion
    apply (hD.preimage e.missingInclusion.isClosedEmbedding.injective.injOn).subset
    intro w hw
    have hn : e.missingInclusion w ∉ Set.range e.inclusion := by
      change e.missingInclusion w ∈ (Set.range e.inclusion)ᶜ
      rw [← e.missing_range]
      exact ⟨w, rfl⟩
    have hbad : e.missingInclusion w ∉ Set.range (e.goodOpen.ι ≫ e.inclusion) := by
      rintro ⟨v, hv⟩
      exact hn ⟨e.goodOpen.ι v, hv⟩
    obtain ⟨v, hv⟩ := e.bad_cover hbad
    refine ⟨v, ?_, hv⟩
    change q (e.boundaryInclusion v) = y
    change q (e.missingInclusion w) = y at hw
    simpa only [hv] using hw
  have : LocallyQuasiFinite (e.missingInclusion ≫ q) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ hf
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
