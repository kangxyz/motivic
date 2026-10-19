module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Boundary.Maps
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Sections.Open
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.CurveSourceChange
/-! # The common source maps to the actual single-shrink diagonal section domain -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme] (r : R)

omit [IsAffine V.toScheme] in
lemma commonNeighborhoodProjection_mem (x : (commonNeighborhoodSource R V r).toScheme) :
    commonNeighborhoodProjection R V r x ∈ PrimeSpectrum.basicOpen r := by
  have h := x.property.2
  rw [fixedPsiSource_eq] at h
  exact h.2

lemma commonNeighborhoodToGraphAmbient_mem (x : commonNeighborhoodAmbient R V r) :
    commonNeighborhoodToGraphAmbient R V r x ∈
      ((neighborhoodProjectiveIso R V).hom ⁻¹ᵁ neighborhoodSerreOpen R V r) := by
  rw [neighborhoodSerreOpen_eq_compact]
  change (commonNeighborhoodToGraphAmbient R V r ≫
    pullback.fst (neighborhoodProjection R V) (ProjectiveSpace.toSpec R _) ≫
      neighborhoodProjection R V) x ∈ PrimeSpectrum.basicOpen r
  have hf : commonNeighborhoodToGraphAmbient R V r ≫
      pullback.fst (neighborhoodProjection R V) (ProjectiveSpace.toSpec R _) ≫
        neighborhoodProjection R V =
      pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _) ≫
        commonNeighborhoodProjection R V r := by
    simp only [commonNeighborhoodToGraphAmbient, pullback.lift_fst_assoc, Category.assoc,
      commonNeighborhoodProjection_graph]
  rw [hf]
  exact commonNeighborhoodProjection_mem R V r
    (pullback.fst (commonNeighborhoodProjection R V r)
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) x)

def commonNeighborhoodToSectionAmbient : commonNeighborhoodAmbient R V r ⟶
    ((neighborhoodProjectiveIso R V).hom ⁻¹ᵁ neighborhoodSerreOpen R V r).toScheme :=
  IsOpenImmersion.lift
    ((neighborhoodProjectiveIso R V).hom ⁻¹ᵁ neighborhoodSerreOpen R V r).ι
    (commonNeighborhoodToGraphAmbient R V r) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact commonNeighborhoodToGraphAmbient_mem R V r x)

@[reassoc (attr := simp)] lemma commonNeighborhoodToSectionAmbient_ι :
    commonNeighborhoodToSectionAmbient R V r ≫
      ((neighborhoodProjectiveIso R V).hom ⁻¹ᵁ neighborhoodSerreOpen R V r).ι =
        commonNeighborhoodToGraphAmbient R V r := IsOpenImmersion.lift_fac _ _ _

variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)

def commonNeighborhoodBoundaryToSection : commonNeighborhoodBoundary R V r ⟶
    ((neighborhoodGraphBoundaryMap R V hV) ⁻¹ᵁ
      ((neighborhoodProjectiveIso R V).hom ⁻¹ᵁ neighborhoodSerreOpen R V r)).toScheme :=
  IsOpenImmersion.lift
    ((neighborhoodGraphBoundaryMap R V hV) ⁻¹ᵁ
      ((neighborhoodProjectiveIso R V).hom ⁻¹ᵁ neighborhoodSerreOpen R V r)).ι
    (commonNeighborhoodBoundaryToGraph R V r hV) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change (commonNeighborhoodBoundaryToGraph R V r hV ≫
      neighborhoodGraphBoundaryMap R V hV) x ∈
      ((neighborhoodProjectiveIso R V).hom ⁻¹ᵁ neighborhoodSerreOpen R V r)
    rw [commonNeighborhoodBoundaryToGraph_fac]
    exact commonNeighborhoodToGraphAmbient_mem R V r (commonNeighborhoodBoundaryMap R V r x))

@[reassoc (attr := simp)] lemma commonNeighborhoodBoundaryToSection_ι :
    commonNeighborhoodBoundaryToSection R V r hV ≫
      ((neighborhoodGraphBoundaryMap R V hV) ⁻¹ᵁ
        ((neighborhoodProjectiveIso R V).hom ⁻¹ᵁ neighborhoodSerreOpen R V r)).ι =
    commonNeighborhoodBoundaryToGraph R V r hV := IsOpenImmersion.lift_fac _ _ _

@[reassoc] lemma commonNeighborhoodBoundaryToSection_fac :
    commonNeighborhoodBoundaryToSection R V r hV ≫
      (neighborhoodGraphBoundaryMap R V hV ∣_
        ((neighborhoodProjectiveIso R V).hom ⁻¹ᵁ neighborhoodSerreOpen R V r)) =
    commonNeighborhoodBoundaryMap R V r ≫ commonNeighborhoodToSectionAmbient R V r := by
  apply (cancel_mono
    ((neighborhoodProjectiveIso R V).hom ⁻¹ᵁ neighborhoodSerreOpen R V r).ι).mp
  simp only [Category.assoc, morphismRestrict_ι, commonNeighborhoodBoundaryToSection_ι_assoc,
    commonNeighborhoodToSectionAmbient_ι, commonNeighborhoodBoundaryToGraph_fac]
end AlgebraicGeometry.RelativeProjectiveLine
