module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Sections.Pencils
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.FiniteFlatPencil
/-! # Construction of the whole finite-flat relative neighborhood pencil -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
  (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
  (r : R)

/-- The polynomial family functional joining the restricted pencil start and end functionals. -/
def NeighborhoodPencilSections.familyFunctional (d : NeighborhoodPencilSections R V hV r) :=
  let q := pullback.fst (commonNeighborhoodProjection R V r)
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
  let j := commonNeighborhoodRetainedInclusion R V r
  familyMap ((j ≫ q) ≫ commonNeighborhoodProjection R V r)
    (pullbackLineBundle j (commonNeighborhoodPencilLine R V r d.lambdaDegree d.psiDegree))
    (Scheme.Modules.Hom.pullbackToUnit
      (d.lambda.pencilStart R V hV r d.lambdaDegree d.psiDegree d.frame d.psiDenominator) j)
    (Scheme.Modules.Hom.pullbackToUnit
      (d.lambda.pencilEnd R V hV r d.lambdaDegree d.psiDegree d.frame d.psiNumerator) j)

/-- The projection from the zero scheme of the family functional to the parameter scheme. -/
def NeighborhoodPencilSections.familyProjection (d : NeighborhoodPencilSections R V hV r) :=
  Scheme.Modules.Hom.zeroInclusion (d.familyFunctional R V hV r) ≫
    parameterMap (commonNeighborhoodProjection R V r)
      (commonNeighborhoodRetainedInclusion R V r ≫
        pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _))

lemma NeighborhoodPencilSections.family_finite_flat (d : NeighborhoodPencilSections R V hV r) :
    IsFinite (d.familyProjection R V hV r) ∧ Flat (d.familyProjection R V hV r) := by
  have := d.psiNumerator_unit
  exact d.lambda.common_family_finite_flat R V hV r d.lambdaDegree d.psiDegree d.frame
    d.psiNumerator d.psiDenominator d.psi_value

/-- Actual sections and their whole polynomial zero family exist near every original base point.
No family finiteness, boundary frames, or section values are premises. -/
theorem exists_neighborhoodFiniteFlatPencil [IsNoetherianRing R] (s : Spec (.of R)) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
      ∃ d : NeighborhoodPencilSections R V hV r,
        IsFinite (d.familyProjection R V hV r) ∧ Flat (d.familyProjection R V hV r) := by
  obtain ⟨r, hr, ⟨d⟩⟩ := exists_neighborhoodPencilSections R V hV s
  exact ⟨r, hr, d, d.family_finite_flat R V hV r⟩
end AlgebraicGeometry.RelativeProjectiveLine
