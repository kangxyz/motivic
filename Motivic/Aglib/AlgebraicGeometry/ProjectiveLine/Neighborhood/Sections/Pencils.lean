/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Pencil.Basic
/-! # Both genuine section pairs on one original base neighborhood -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
  (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)

/-- Actual sections, not assumed correspondence endpoints or family properties. -/
structure NeighborhoodPencilSections (r : R) where
  /-- The nonnegative twisting degree of the lambda section pair. -/
  lambdaDegree : ℕ
  /-- The nonnegative twisting degree of the psi section pair. -/
  psiDegree : ℕ
  /-- The original full-boundary twist frame at the lambda degree. -/
  frame : neighborhoodFrame R V r lambdaDegree
  /-- The neighborhood section pair at the lambda degree with the chosen boundary frame. -/
  lambda : NeighborhoodSectionPair R V hV r lambdaDegree frame
  /-- The numerator section map of the fixed-source psi pair. -/
  psiNumerator : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
    (fixedPsiTwistLine R r psiDegree).val
  /-- The denominator section map of the fixed-source psi pair. -/
  psiDenominator : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
    (fixedPsiTwistLine R r psiDegree).val
  psi_value : pullbackSectionMap (fixedPsiBoundaryMap R r V) psiNumerator =
    (fixedPsiBoundaryUnit R V r).hom ≫
      pullbackSectionMap (fixedPsiBoundaryMap R r V) psiDenominator
  psiNumerator_unit : IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) psiNumerator)
  psiDenominator_unit : IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) psiDenominator)
  psiNumerator_finite_flat :
    FixedPsiLineSectionFiniteFlat R r V (fixedPsiTwistLine R r psiDegree) psiNumerator
  psiDenominator_finite_flat :
    FixedPsiLineSectionFiniteFlat R r V (fixedPsiTwistLine R r psiDegree) psiDenominator

/-- The common original-base shrink and both section pairs are constructed from the input
neighborhood. The punctured source is exactly the whole multiplicative line over that shrink. -/
theorem exists_neighborhoodPencilSections [IsNoetherianRing R] (s : Spec (.of R)) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧ Nonempty (NeighborhoodPencilSections R V hV r) := by
  obtain ⟨r, hr, e, L, hL⟩ := exists_neighborhoodFiniteFlatSectionPair_near R V hV s
  obtain ⟨d, _, _⟩ := hL L le_rfl
  obtain ⟨N, hN⟩ := exists_fixedPsiNormalizedSectionPair R r V hV e
  obtain ⟨n, t, hn, hnu, htu, hnf, htf⟩ := hN N le_rfl
  exact ⟨r, hr, ⟨⟨L, N, e L, d, n, t, hn, hnu, htu, hnf, htf⟩⟩⟩
end AlgebraicGeometry.RelativeProjectiveLine
