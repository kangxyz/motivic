module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Graph.Boundary
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoproductUnitEndomorphism
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateProductPullback
/-! # The canonical relative graph section in its original full-boundary frame -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens)
  (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)

/-- The zero-boundary product map to the original affine boundary coordinate product. -/
def neighborhoodBoundaryCoordinateMap :
    pullback (neighborhoodProjection R V) (neighborhoodZero R V hV ≫
      neighborhoodInclusion R V ≫ ProjectiveSpace.toSpec R _) ⟶
    pullback (Scheme.Hom.boundaryLineProjection R)
      (Scheme.Hom.boundaryCoordinateMap R R (Polynomial.evalRingHom 0) ≫
        Scheme.Hom.boundaryLineProjection R) :=
  (pullback.congrHom (neighborhoodProjection_eq R V)
    (by rw [← Category.assoc, neighborhoodZero_inclusion];
        simp only [zeroSection, Category.assoc, chart_toSpec,
          Scheme.Hom.boundaryCoordinateMap, Scheme.Hom.boundaryLineProjection])).hom ≫
    Scheme.Hom.boundaryProductMap (Scheme.Hom.boundaryLineProjection R) V.ι
      (Scheme.Hom.boundaryCoordinateMap R R (Polynomial.evalRingHom 0))

/-- The canonical dual graph section expressed in the full graph-boundary trivialization. -/
def neighborhoodBoundaryCoordinate :
    SheafOfModules.unit (neighborhoodGraphBoundarySource R V hV).ringCatSheaf ⟶
      SheafOfModules.unit (neighborhoodGraphBoundarySource R V hV).ringCatSheaf :=
  pullbackSectionMap (neighborhoodGraphBoundaryMap R V hV)
    (canonicalDualHom _ (neighborhoodGraphLine R V).val
      (Scheme.Hom.idealInclusion (Scheme.Hom.compactificationGraph
        (ProjectiveSpace.toSpec R _) (neighborhoodInclusion R V)))) ≫
    (neighborhoodGraphBoundaryIso R V hV).hom

lemma neighborhoodBoundaryCoordinate_missing :
    Scheme.Hom.unitEndomorphismPullback coprod.inl
      (neighborhoodBoundaryCoordinate R V hV) = 𝟙 _ := by
  have h := Scheme.Hom.unitEndomorphismPullback_coprod_inl_coordinate
    (Scheme.Hom.infinityProductMap (ProjectiveSpace.toSpec R _)
      (neighborhoodInclusion R V) (neighborhoodBoundaryInclusion R V))
    (Scheme.Hom.graphBoundaryRestriction (ProjectiveSpace.toSpec R _)
      (neighborhoodInclusion R V) (neighborhoodZero R V hV))
    (neighborhoodGraphDivisor R V).val
    (canonicalDualHom _ (neighborhoodGraphLine R V).val
      (Scheme.Hom.idealInclusion (Scheme.Hom.compactificationGraph
        (ProjectiveSpace.toSpec R _) (neighborhoodInclusion R V))))
    (neighborhoodGraphBoundaryIso R V hV) (neighborhoodMissingDivisorIso R V)
    (neighborhoodGraphBoundaryIso_missing R V hV)
  exact h.trans (Scheme.Hom.infinityBoundaryDivisorIso_canonical
    (ProjectiveSpace.toSpec R _) (neighborhoodInclusion R V)
    (neighborhoodBoundaryInclusion R V) (neighborhoodInclusion_disjoint R V)
    (neighborhoodGraphLine R V).property)

lemma neighborhoodBoundaryCoordinate_zero :
    Scheme.Hom.unitEndomorphismPullback coprod.inr
      (neighborhoodBoundaryCoordinate R V hV) =
    Scheme.Hom.boundaryCoordinateEndomorphism R R (Polynomial.evalRingHom 0)
      (neighborhoodBoundaryCoordinateMap R V hV) := by
  have h := Scheme.Hom.unitEndomorphismPullback_coprod_inr_coordinate
    (Scheme.Hom.infinityProductMap (ProjectiveSpace.toSpec R _)
      (neighborhoodInclusion R V) (neighborhoodBoundaryInclusion R V))
    (Scheme.Hom.graphBoundaryRestriction (ProjectiveSpace.toSpec R _)
      (neighborhoodInclusion R V) (neighborhoodZero R V hV))
    (neighborhoodGraphDivisor R V).val
    (canonicalDualHom _ (neighborhoodGraphLine R V).val
      (Scheme.Hom.idealInclusion (Scheme.Hom.compactificationGraph
        (ProjectiveSpace.toSpec R _) (neighborhoodInclusion R V))))
    (neighborhoodGraphBoundaryIso R V hV) (neighborhoodZeroDivisorIso R V hV)
    (neighborhoodGraphBoundaryIso_zero R V hV)
  have hc := Scheme.Hom.compactificationBoundaryDivisorIso_coordinate R R
    (Polynomial.evalRingHom 0) (ProjectiveSpace.toSpec R _) (neighborhoodInclusion R V)
    V.ι (neighborhoodProjection_eq R V) (neighborhoodZero R V hV)
    (neighborhoodZero_ι R V hV) (neighborhoodZero_isPullback R V hV)
    (neighborhoodGraphLine R V).property
  exact h.trans (hc.trans (Scheme.Hom.boundaryCoordinateEndomorphism_comp R R
    (Polynomial.evalRingHom 0) _ _).symm)
end AlgebraicGeometry.RelativeProjectiveLine
