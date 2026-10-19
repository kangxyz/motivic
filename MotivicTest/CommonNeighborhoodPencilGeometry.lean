module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Pencil.Geometry
/-! # Direct consumers of the actual common relative pencil geometry -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RelativeProjectiveLine

example (R : Type) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens) (r : R)
    [IsAffine V.toScheme]
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V) :
    IsAffine (commonNeighborhoodSource R V r).toScheme ∧
      IsAffine (commonNeighborhoodRetainedCurve R V r) ∧
      IsProper (pullback.fst (commonNeighborhoodProjection R V r)
        (ProjectiveSpace.toSpec R (ULift (Fin 2)))) ∧
      IsClosedImmersion (commonNeighborhoodBoundaryMap R V r) ∧
      SmoothOfRelativeDimension 1 (commonNeighborhoodRetainedInclusion R V r ≫
        pullback.fst (commonNeighborhoodProjection R V r)
          (ProjectiveSpace.toSpec R (ULift (Fin 2)))) ∧
      ∀ x : commonNeighborhoodAmbient R V r,
        x ∈ Set.range (commonNeighborhoodRetainedInclusion R V r) ∨
          x ∈ Set.range (commonNeighborhoodBoundaryMap R V r) :=
  ⟨commonNeighborhoodSource_affine R V r,
    commonNeighborhoodRetainedCurve_affine R V r,
    commonNeighborhoodProjection_proper R V r,
    commonNeighborhoodBoundary_closed R V r hV,
    commonNeighborhoodRetainedCurve_smooth R V r,
    commonNeighborhoodRetained_boundary_cover R V r⟩
