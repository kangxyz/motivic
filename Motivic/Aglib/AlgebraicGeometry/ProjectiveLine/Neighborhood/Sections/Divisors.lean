/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Retained.Geometry
/-! # Actual section divisors after the single original base shrink -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
variable (r : R)

/-- The inverse image of the base principal open defined by `r` in the neighborhood. -/
abbrev neighborhoodSourceOpen := neighborhoodProjection R V ⁻¹ᵁ PrimeSpectrum.basicOpen r
/-- The inverse image of the source principal open in the graph ambient scheme. -/
abbrev neighborhoodCompactOpen :=
  (pullback.fst (neighborhoodProjection R V) (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) ⁻¹ᵁ
    neighborhoodSourceOpen R V r
/-- The graph ambient projection restricted over the source principal open. -/
abbrev neighborhoodRestrictedProjection :=
  (pullback.fst (neighborhoodProjection R V) (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) ∣_
    neighborhoodSourceOpen R V r
/-- The whole graph-boundary map restricted over the compact open. -/
abbrev neighborhoodRestrictedBoundary :=
  neighborhoodGraphBoundaryMap R V hV ∣_ neighborhoodCompactOpen R V r
/-- The retained-curve map restricted over the compact open. -/
abbrev neighborhoodRestrictedRetained :=
  neighborhoodRetainedInclusion R V ∣_ neighborhoodCompactOpen R V r

lemma neighborhoodSourceOpen_affine : IsAffine (neighborhoodSourceOpen R V r).toScheme := by
  have : IsAffineHom (neighborhoodProjection R V) := isAffineHom_of_isAffine _
  exact (IsAffineOpen.Spec_basicOpen (R := .of R) r).preimage (neighborhoodProjection R V)

lemma neighborhoodRestrictedRetained_affine :
    IsAffine ((neighborhoodRetainedInclusion R V) ⁻¹ᵁ
      neighborhoodCompactOpen R V r).toScheme := by
  have := neighborhoodRetainedCurve_affine R V
  let f := neighborhoodRetainedInclusion R V ≫
    pullback.fst (neighborhoodProjection R V) (ProjectiveSpace.toSpec R _) ≫
      neighborhoodProjection R V
  have : IsAffineHom f := isAffineHom_of_isAffine _
  exact (IsAffineOpen.Spec_basicOpen (R := .of R) r).preimage f

omit [IsAffine V.toScheme] in
lemma neighborhoodRestrictedRetained_smooth : SmoothOfRelativeDimension 1
    (neighborhoodRestrictedRetained R V r ≫ neighborhoodRestrictedProjection R V r) := by
  change SmoothOfRelativeDimension 1
    ((neighborhoodRetainedInclusion R V ∣_ neighborhoodCompactOpen R V r) ≫
      (pullback.fst (neighborhoodProjection R V) (ProjectiveSpace.toSpec R _) ∣_
        neighborhoodSourceOpen R V r))
  rw [← morphismRestrict_comp]
  have h := neighborhoodRetainedCurve_smooth R V
  exact MorphismProperty.of_isPullback (isPullback_morphismRestrict _ _).flip h

omit [IsAffine V.toScheme] in
lemma neighborhoodRestricted_boundary_cover :
    ∀ x : (neighborhoodCompactOpen R V r).toScheme,
      x ∈ Set.range (neighborhoodRestrictedRetained R V r) ∨
        x ∈ Set.range (neighborhoodRestrictedBoundary R V hV r) := by
  intro x
  rcases neighborhoodRetained_boundary_cover R V hV x.val with ⟨y, hy⟩ | ⟨y, hy⟩
  · left
    refine ⟨⟨y, ?_⟩, ?_⟩
    · change neighborhoodRetainedInclusion R V y ∈ neighborhoodCompactOpen R V r
      rw [hy]
      exact x.property
    · apply Subtype.ext
      exact (morphismRestrict_base_coe _ _ _).trans hy
  · right
    refine ⟨⟨y, ?_⟩, ?_⟩
    · change neighborhoodGraphBoundaryMap R V hV y ∈ neighborhoodCompactOpen R V r
      rw [hy]
      exact x.property
    · apply Subtype.ext
      exact (morphismRestrict_base_coe _ _ _).trans hy

/-- The entire original zero scheme is finite flat, not just its support or reduction. -/
theorem neighborhoodSection_whole_zero_finite_flat
    (L : LineBundle (neighborhoodCompactOpen R V r).toScheme)
    (a : SheafOfModules.unit (neighborhoodCompactOpen R V r).toScheme.ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap (neighborhoodRestrictedBoundary R V hV r) a)] :
    IsFinite (Scheme.Modules.Hom.zeroInclusion (sectionDualFunctional _ L a) ≫
      neighborhoodRestrictedProjection R V r) ∧
    Flat (Scheme.Modules.Hom.zeroInclusion (sectionDualFunctional _ L a) ≫
      neighborhoodRestrictedProjection R V r) := by
  have := neighborhoodSourceOpen_affine R V r
  have := neighborhoodRestrictedRetained_affine R V r
  have := neighborhoodRestrictedRetained_smooth R V r
  exact sectionDualFunctional_whole_zero_finite_flat (neighborhoodRestrictedBoundary R V hV r)
    (neighborhoodRestrictedProjection R V r) (neighborhoodRestrictedRetained R V r) L a
    (neighborhoodRestricted_boundary_cover R V hV r)
/-- The retained equation and the full zero scheme, without discarding multiplicities. -/
theorem neighborhoodSection_finite_mono_flat
    (L : LineBundle (neighborhoodCompactOpen R V r).toScheme)
    (a : SheafOfModules.unit (neighborhoodCompactOpen R V r).toScheme.ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap (neighborhoodRestrictedBoundary R V hV r) a)] :
    let q := neighborhoodRestrictedProjection R V r
    let j := neighborhoodRestrictedRetained R V r
    let t := sectionDualFunctional _ L a
    IsFinite (Scheme.Modules.Hom.zeroInclusion t ≫ q) ∧
      Flat (Scheme.Modules.Hom.zeroInclusion t ≫ q) ∧
      Set.range (Scheme.Modules.Hom.zeroInclusion t) ⊆ Set.range j ∧
      IsFinite (Scheme.Modules.Hom.zeroInclusion (Scheme.Modules.Hom.pullbackToUnit t j) ≫ j ≫ q) ∧
      Mono (Scheme.Modules.Hom.pullbackToUnit t j) ∧
      Flat (Scheme.Modules.Hom.zeroInclusion (Scheme.Modules.Hom.pullbackToUnit t j) ≫ j ≫ q) := by
  have := neighborhoodSourceOpen_affine R V r
  have := neighborhoodRestrictedRetained_affine R V r
  have := neighborhoodRestrictedRetained_smooth R V r
  obtain ⟨hf, hfl⟩ := neighborhoodSection_whole_zero_finite_flat R V hV r L a
  exact ⟨hf, hfl,
    sectionDualFunctional_zero_range (neighborhoodRestrictedBoundary R V hV r)
      (neighborhoodRestrictedRetained R V r) L a (neighborhoodRestricted_boundary_cover R V hV r),
    sectionDualFunctional_finite_mono_flat_on_open (neighborhoodRestrictedBoundary R V hV r)
      (neighborhoodRestrictedProjection R V r) (neighborhoodRestrictedRetained R V r) L a
      (neighborhoodRestricted_boundary_cover R V hV r)⟩
end AlgebraicGeometry.RelativeProjectiveLine
