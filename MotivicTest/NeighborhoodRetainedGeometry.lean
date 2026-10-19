module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Retained.Geometry
/-! The original punctured target is affine and the full boundary covers its complement. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
universe u
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
example : IsAffine (neighborhoodRetainedCurve R V) := neighborhoodRetainedCurve_affine R V
example (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V) :
    ∀ x : neighborhoodGraphAmbient R V,
      x ∈ Set.range (neighborhoodRetainedInclusion R V) ∨
        x ∈ Set.range (neighborhoodGraphBoundaryMap R V hV) :=
  neighborhoodRetained_boundary_cover R V hV
#print axioms neighborhoodRetained_boundary_cover
#print axioms neighborhoodRetained_projection_smooth
#print axioms neighborhoodRetainedCurve_affine
