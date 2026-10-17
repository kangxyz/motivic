module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodSectionDivisors
/-! The entire zero scheme remains finite flat after the original base shrink. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
open Scheme.Modules Scheme.Modules.Invertible
universe u
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
example (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
    (r : R) (L : LineBundle (neighborhoodCompactOpen R V r).toScheme)
    (a : SheafOfModules.unit (neighborhoodCompactOpen R V r).toScheme.ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap (neighborhoodRestrictedBoundary R V hV r) a)] :
    IsFinite (Scheme.Modules.Hom.zeroInclusion (sectionDualFunctional _ L a) ≫
      neighborhoodRestrictedProjection R V r) ∧
    Flat (Scheme.Modules.Hom.zeroInclusion (sectionDualFunctional _ L a) ≫
      neighborhoodRestrictedProjection R V r) :=
  neighborhoodSection_whole_zero_finite_flat R V hV r L a
#print axioms neighborhoodSection_finite_mono_flat
