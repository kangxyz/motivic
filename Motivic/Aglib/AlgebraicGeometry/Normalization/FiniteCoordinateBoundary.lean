/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.FiniteCoordinateProjectiveLine
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.ZeroNeighborhoodBoundary
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.RetainedBoundaryNeighborhood

/-! # The full boundary of the original finite coordinate compactification -/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry

/-- The complete closed complement, with any closed scheme structure, is finite
over the original base when the unchanged source is the full affine-chart preimage. -/
theorem finite_boundary_of_full_projectiveLine_chart
    (R : Type u) [CommRing R] {N D : Scheme.{u}}
    (π : N ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsFinite π]
    (b : D ⟶ N) [IsClosedImmersion b]
    (hb : ∀ x : D, π (b x) ∉ Set.range (RelativeProjectiveLine.chart R 0)) :
    IsFinite (b ≫ π ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  let d := RelativeProjectiveLine.neighborhoodBoundaryInclusion R ⊤
  have : IsFinite (d ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) :=
    RelativeProjectiveLine.neighborhoodBoundary_finite R ⊤ (by intro x hx; trivial)
  let g := b ≫ π
  let q := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
  have : IsFinite g := by dsimp [g]; infer_instance
  have : IsProper (g ≫ q) := by dsimp [q]; infer_instance
  have hp : ∀ s : Spec (.of R), ((g ≫ q) ⁻¹' {s}).Finite := by
    intro s
    have hD : (d '' ((d ≫ q) ⁻¹' {s})).Finite :=
      ((d ≫ q).finite_preimage_singleton s).image d
    apply (g.finite_preimage hD).subset
    intro x hx
    have hxD : g x ∈ Set.range d := by
      rw [RelativeProjectiveLine.range_neighborhoodBoundaryInclusion]
      change π (b x) ∉ RelativeProjectiveLine.projectiveNeighborhood R ⊤
      intro hn
      obtain ⟨y, _, hy⟩ := hn
      exact hb x ⟨y, hy⟩
    obtain ⟨z, hz⟩ := hxD
    refine ⟨z, ?_, hz⟩
    change q (d z) = s
    change q (g x) = s at hx
    simpa only [hz] using hx
  have : LocallyQuasiFinite (g ≫ q) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ hp
  exact IsFinite.of_isProper_of_locallyQuasiFinite (g ≫ q)

/-- Apply the finite boundary theorem to the actual complete complement of the
original source open, not a chosen smaller boundary or its components. -/
theorem finite_retainedBoundary_of_full_projectiveLine_chart
    (R : Type u) [CommRing R] {N X : Scheme.{u}}
    (π : N ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsFinite π]
    (i : X ⟶ N) [IsOpenImmersion i]
    (hi : Set.range i = π ⁻¹' Set.range (RelativeProjectiveLine.chart R 0)) :
    IsFinite (Scheme.RelativeCurve.retainedBoundaryInclusion i.opensRange ≫ π ≫
      ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  apply finite_boundary_of_full_projectiveLine_chart R π
  intro x hx
  have hn : Scheme.RelativeCurve.retainedBoundaryInclusion i.opensRange x ∉ i.opensRange := by
    have hm : Scheme.RelativeCurve.retainedBoundaryInclusion i.opensRange x ∈
        Set.range (Scheme.RelativeCurve.retainedBoundaryInclusion i.opensRange) := ⟨x, rfl⟩
    rw [Scheme.RelativeCurve.range_retainedBoundaryInclusion] at hm
    exact hm
  apply hn
  change _ ∈ Set.range i
  rw [hi]
  exact hx

end AlgebraicGeometry
