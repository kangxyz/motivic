module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.CommonNeighborhoodBoundary
/-! # Original ambient factor equations for the whole common lambda and psi boundary -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens) (r : R)

def commonNeighborhoodMissingInclusion : commonNeighborhoodMissing R V r ⟶
    commonNeighborhoodAmbient R V r :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ neighborhoodBoundaryInclusion R V)
    (by rw [Category.assoc]; exact pullback.condition)

def commonNeighborhoodZeroInclusion : commonNeighborhoodZero R V r ⟶
    commonNeighborhoodAmbient R V r :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ zeroSection R) (by
    rw [Category.assoc]
    simpa only [zeroSection, Category.assoc, chart_toSpec,
      Scheme.Hom.boundaryCoordinateMap, Scheme.Hom.boundaryLineProjection] using
      (pullback.condition (f := commonNeighborhoodProjection R V r)
        (g := Scheme.Hom.boundaryCoordinateMap R R (Polynomial.evalRingHom 0) ≫
          Scheme.Hom.boundaryLineProjection R)))

def commonNeighborhoodBoundaryMap : commonNeighborhoodBoundary R V r ⟶
    commonNeighborhoodAmbient R V r :=
  coprod.desc (commonNeighborhoodMissingInclusion R V r) (commonNeighborhoodZeroInclusion R V r)

variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)

@[reassoc] lemma commonNeighborhoodBoundaryToGraph_fac :
    commonNeighborhoodBoundaryToGraph R V r hV ≫ neighborhoodGraphBoundaryMap R V hV =
      commonNeighborhoodBoundaryMap R V r ≫ commonNeighborhoodToGraphAmbient R V r := by
  apply coprod.hom_ext
  · simp only [commonNeighborhoodBoundaryToGraph, coprod.inl_map_assoc,
      neighborhoodGraphBoundaryMap, Scheme.Hom.fullBoundaryProductMap, coprod.inl_desc,
      commonNeighborhoodBoundaryMap, coprod.inl_desc_assoc]
    apply pullback.hom_ext <;>
      simp [commonNeighborhoodMissingToGraph, Scheme.Hom.infinityProductMap,
        commonNeighborhoodMissingInclusion, commonNeighborhoodToGraphAmbient]
  · simp only [commonNeighborhoodBoundaryToGraph, coprod.inr_map_assoc,
      neighborhoodGraphBoundaryMap, Scheme.Hom.fullBoundaryProductMap, coprod.inr_desc,
      commonNeighborhoodBoundaryMap, coprod.inr_desc_assoc]
    apply pullback.hom_ext <;>
      simp [commonNeighborhoodZeroToGraph, Scheme.Hom.graphBoundaryRestriction,
        commonNeighborhoodZeroInclusion, commonNeighborhoodToGraphAmbient, zeroSection]

@[reassoc] lemma commonNeighborhoodBoundaryToPsi_fac :
    commonNeighborhoodBoundaryToPsi R V r ≫ fixedPsiBoundaryMap R r V =
      commonNeighborhoodBoundaryMap R V r ≫ commonNeighborhoodToPsiAmbient R V r := by
  apply coprod.hom_ext
  · simp only [commonNeighborhoodBoundaryToPsi, coprod.inl_map_assoc,
      fixedPsiBoundaryMap, coprod.inl_desc, commonNeighborhoodBoundaryMap, coprod.inl_desc_assoc]
    apply pullback.hom_ext <;>
      simp [commonNeighborhoodMissingToPsi, fixedPsiMissingMap, fixedPsiProductBoundaryMap,
        commonNeighborhoodMissingInclusion, commonNeighborhoodToPsiAmbient]
  · simp only [commonNeighborhoodBoundaryToPsi, coprod.inr_map_assoc,
      fixedPsiBoundaryMap, coprod.inr_desc, commonNeighborhoodBoundaryMap, coprod.inr_desc_assoc]
    apply pullback.hom_ext <;>
      simp [commonNeighborhoodZeroToPsi, fixedPsiZeroMap,
        commonNeighborhoodZeroInclusion, commonNeighborhoodToPsiAmbient]
end AlgebraicGeometry.RelativeProjectiveLine
