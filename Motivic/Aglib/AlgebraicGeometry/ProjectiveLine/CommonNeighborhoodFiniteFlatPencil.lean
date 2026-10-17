module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.CommonNeighborhoodPencil
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.CommonNeighborhoodPencilGeometry
public import Motivic.Aglib.AlgebraicGeometry.PolynomialPencilFiniteFlat
/-! # Finite-flatness of the actual relative polynomial pencil on the original retained target -/
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
  (r : R) (l m : ℕ) (e : neighborhoodFrame R V r l)

theorem NeighborhoodSectionPair.common_family_finite_flat
    (d : NeighborhoodSectionPair R V hV r l e)
    (n t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val)
    [IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) n)]
    (hn : pullbackSectionMap (fixedPsiBoundaryMap R r V) n =
      (fixedPsiBoundaryUnit R V r).hom ≫ pullbackSectionMap (fixedPsiBoundaryMap R r V) t) :
    let q := pullback.fst (commonNeighborhoodProjection R V r)
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
    let j := commonNeighborhoodRetainedInclusion R V r
    let f := familyMap ((j ≫ q) ≫ commonNeighborhoodProjection R V r)
      (pullbackLineBundle j (commonNeighborhoodPencilLine R V r l m))
      (Scheme.Modules.Hom.pullbackToUnit (d.pencilStart R V hV r l m e t) j)
      (Scheme.Modules.Hom.pullbackToUnit (d.pencilEnd R V hV r l m e n) j)
    IsFinite (Scheme.Modules.Hom.zeroInclusion f ≫
      parameterMap (commonNeighborhoodProjection R V r) (j ≫ q)) ∧
    Flat (Scheme.Modules.Hom.zeroInclusion f ≫
      parameterMap (commonNeighborhoodProjection R V r) (j ≫ q)) := by
  have := d.pencilStart_boundary_isIso R V hV r l m e n t hn
  have := commonNeighborhoodSource_affine R V r
  have := commonNeighborhoodRetainedCurve_affine R V r
  have := commonNeighborhoodRetainedCurve_smooth R V r
  exact retained_familySource_finite_flat (commonNeighborhoodProjection R V r)
    (pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _))
    (commonNeighborhoodRetainedInclusion R V r) (commonNeighborhoodBoundaryMap R V r)
    (commonNeighborhoodPencilLine R V r l m)
    (d.pencilStart R V hV r l m e t) (d.pencilEnd R V hV r l m e n)
    (d.pencil_boundary R V hV r l m e n t hn)
    (commonNeighborhoodRetained_boundary_cover R V r)
end AlgebraicGeometry.RelativeProjectiveLine
