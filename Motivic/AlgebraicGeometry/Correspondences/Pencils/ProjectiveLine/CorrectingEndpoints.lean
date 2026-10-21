/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Sections.PencilData
public import Motivic.AlgebraicGeometry.Correspondences.Pencils.NormalizedCurve.CorrectingEndpoints
/-! # Actual correcting correspondences over a neighborhood of the original relative base point -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Motivic
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (k R : Type u) [Field k] [CommRing R]
  (b : Spec (.of R) ⟶ Spec (.of k)) [Smooth b]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
  (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)

/-- Both endpoints come from the actual whole finite-flat pencil; no correspondence is supplied. -/
theorem NeighborhoodPencilSections.correctingEndpoints {r : R}
    (P : NeighborhoodPencilSections R V hV r) :
    HasCorrectingEndpoints (neighborhoodPencilAlpha k R b V r)
      (neighborhoodPencilBeta k R b V r) (neighborhoodPencilGraph k R b V r) :=
  hasCorrectingEndpoints_of_data (P.correspondenceData k R b V hV r)

include hV in
/-- The original relative open neighborhood produces a correcting homotopy after one base
shrink. The source is the whole punctured line over that shrink, and the target is unchanged. -/
theorem exists_neighborhoodCorrectingEndpoints [IsNoetherianRing R] (s : Spec (.of R)) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
      HasCorrectingEndpoints (neighborhoodPencilAlpha k R b V r)
        (neighborhoodPencilBeta k R b V r) (neighborhoodPencilGraph k R b V r) := by
  obtain ⟨r, hr, ⟨P⟩⟩ := exists_neighborhoodPencilSections R V hV s
  exact ⟨r, hr, P.correctingEndpoints k R b V hV⟩
end AlgebraicGeometry.RelativeProjectiveLine
