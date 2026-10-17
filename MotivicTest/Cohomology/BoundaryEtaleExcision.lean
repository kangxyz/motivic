module

public import Motivic.Cohomology.A1.BoundaryEtaleExcision

/-! # Actual boundary-sheaf étale excision regression tests

No homotopy invariance, purity, field assumption, or global quotient excision
is provided. Both targets are the original small-site boundary cokernels.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic Motivic.FiniteEtaleSite
universe u
namespace MotivicTest.BoundaryEtaleExcision

variable {B : Scheme.{u}} {U Y U' Y' Z : SmoothSite B}
  (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
  (j : U ⟶ Y) (p : Y' ⟶ Y) (j' : U' ⟶ Y') (q : U' ⟶ U)
  [Etale p.left] [IsSeparated p.left] [QuasiCompact p.left]
  (hpb : IsPullback q j' j p)

/-- Transport across the actual lifted closed source of the adapted-coordinate square. -/
def transport (i : Z ⟶ Y) (i' : Z ⟶ Y') (hi : i' ≫ p = i) :
    boundaryCokernel F j i ≅ boundaryCokernel F j' i' := by
  subst i
  exact boundaryEtaleExcisionIso F j p j' q hpb i'

example :
    (etaleRestriction p.left).map (cokernel.π (restrictionToDirectImage F j)) ≫
        (boundaryAmbientEtaleIso F j p j' q hpb).hom =
      (etalePuncturedCoefficientIso F j p j' q hpb).hom ≫
        cokernel.π (restrictionToDirectImage F j') :=
  boundaryAmbientEtaleIso_π F j p j' q hpb

example : inverseImage p.left ≅ etaleRestriction p.left :=
  inverseImageEtaleIso p.left

end MotivicTest.BoundaryEtaleExcision
