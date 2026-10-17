module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.CommonNeighborhoodGraphFamily
/-! # The whole finite-flat family in the original graph-times-pole coefficient -/
set_option linter.hashCommand false
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

example
    {K : Type u} [Field K] (bS : (commonNeighborhoodSource R V r).toScheme ⟶ Spec (.of K))
    (d : NeighborhoodSectionPair R V hV r l e)
    (n t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val)
    [IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) n)]
    (hn : pullbackSectionMap (fixedPsiBoundaryMap R r V) n =
      (fixedPsiBoundaryUnit R V r).hom ≫ pullbackSectionMap (fixedPsiBoundaryMap R r V) t) :
    let j := commonNeighborhoodRetainedInclusion R V r
    let p := j ≫ pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _)
    let a := Scheme.Modules.Hom.productSection
      (Scheme.Hom.idealInclusion (commonNeighborhoodRetainedGraph R V r))
      (Scheme.Modules.Hom.pullbackToUnit (d.poleFunctional R V hV r l m e t) j)
    let c := (commonNeighborhoodRetainedPencilIso R V r l m).hom ≫
      Scheme.Modules.Hom.pullbackToUnit (d.pencilEnd R V hV r l m e n) j
    let f := familyMap (p ≫ bS) (commonNeighborhoodGraphDomainLine R V r l m) a c
    IsFinite (Scheme.Modules.Hom.zeroInclusion f ≫ parameterMap bS p) ∧
      Flat (Scheme.Modules.Hom.zeroInclusion f ≫ parameterMap bS p) :=
  d.graph_family_finite_flat R V hV r l m e bS n t hn
#print axioms NeighborhoodSectionPair.graph_family_finite_flat
#print axioms NeighborhoodSectionPair.retainedPencilIso_start
#print axioms NeighborhoodSectionPair.pole_finite_mono_flat
end AlgebraicGeometry.RelativeProjectiveLine
