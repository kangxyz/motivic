module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Retained.SourceChange
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Sections.FiniteFlat
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Sections.OpenPair
/-! # The retained common curve maps to the literal lambda Serre section domain -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens)
  [IsAffine V.toScheme] (r : R)

def commonNeighborhoodRetainedToSection : commonNeighborhoodRetainedCurve R V r ⟶
    (neighborhoodRetainedInclusion R V ⁻¹ᵁ neighborhoodSectionOpen R V r).toScheme :=
  IsOpenImmersion.lift
    (neighborhoodRetainedInclusion R V ⁻¹ᵁ neighborhoodSectionOpen R V r).ι
    (commonNeighborhoodRetainedToGraph R V r) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      change (commonNeighborhoodRetainedToGraph R V r ≫
        neighborhoodRetainedInclusion R V) x ∈ neighborhoodSectionOpen R V r
      rw [commonNeighborhoodRetainedToGraph_inclusion]
      exact commonNeighborhoodToGraphAmbient_mem R V r
        (commonNeighborhoodRetainedInclusion R V r x))

@[reassoc (attr := simp)] lemma commonNeighborhoodRetainedToSection_ι :
    commonNeighborhoodRetainedToSection R V r ≫
      (neighborhoodRetainedInclusion R V ⁻¹ᵁ neighborhoodSectionOpen R V r).ι =
        commonNeighborhoodRetainedToGraph R V r := IsOpenImmersion.lift_fac _ _ _

@[reassoc] lemma commonNeighborhoodRetainedToSection_inclusion :
    commonNeighborhoodRetainedToSection R V r ≫
      (neighborhoodRetainedInclusion R V ∣_ neighborhoodSectionOpen R V r) =
    commonNeighborhoodRetainedInclusion R V r ≫ commonNeighborhoodToSectionAmbient R V r := by
  apply (cancel_mono (neighborhoodSectionOpen R V r).ι).mp
  simp only [Category.assoc, morphismRestrict_ι,
    commonNeighborhoodRetainedToSection_ι_assoc, commonNeighborhoodToSectionAmbient_ι,
    commonNeighborhoodRetainedToGraph_inclusion]

lemma commonNeighborhoodRetainedToSection_isPullback :
    IsPullback (commonNeighborhoodRetainedToSection R V r)
      (commonNeighborhoodRetainedInclusion R V r)
      (neighborhoodRetainedInclusion R V ∣_ neighborhoodSectionOpen R V r)
      (commonNeighborhoodToSectionAmbient R V r) := by
  apply IsPullback.of_right
    (h₁₂ := (neighborhoodRetainedInclusion R V ⁻¹ᵁ neighborhoodSectionOpen R V r).ι)
    (h₂₂ := (neighborhoodSectionOpen R V r).ι)
  · simpa only [commonNeighborhoodRetainedToSection_ι, commonNeighborhoodToSectionAmbient_ι]
      using commonNeighborhoodRetainedToGraph_inclusion_isPullback R V r
  · exact commonNeighborhoodRetainedToSection_inclusion R V r
  · exact (isPullback_morphismRestrict _ _).flip

instance : IsOpenImmersion (commonNeighborhoodRetainedToSection R V r) :=
  MorphismProperty.of_isPullback (commonNeighborhoodRetainedToSection_isPullback R V r).flip
    inferInstance

/-- The same original source inclusion, factored through precisely D(r). -/
def commonNeighborhoodToSectionSource : (commonNeighborhoodSource R V r).toScheme ⟶
    (neighborhoodSourceOpen R V r).toScheme :=
  IsOpenImmersion.lift (neighborhoodSourceOpen R V r).ι (commonNeighborhoodToV R V r) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change (commonNeighborhoodToV R V r ≫ neighborhoodProjection R V) x ∈
      PrimeSpectrum.basicOpen r
    rw [← commonNeighborhoodProjection_graph]
    exact commonNeighborhoodProjection_mem R V r x)

omit [IsAffine V.toScheme] in
@[reassoc (attr := simp)] lemma commonNeighborhoodToSectionSource_ι :
    commonNeighborhoodToSectionSource R V r ≫ (neighborhoodSourceOpen R V r).ι =
      commonNeighborhoodToV R V r := IsOpenImmersion.lift_fac _ _ _

/-- The actual structural morphism used by the original lambda finite-flat factors. -/
abbrev commonNeighborhoodSectionProjection :=
  ((neighborhoodGraphAmbient R V).isoOfEq (neighborhoodSerreOpen_eq_compact R V r)).hom ≫
    neighborhoodRestrictedProjection R V r

@[reassoc] lemma commonNeighborhoodToSectionAmbient_projection :
    commonNeighborhoodToSectionAmbient R V r ≫ commonNeighborhoodSectionProjection R V r =
      pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _) ≫
        commonNeighborhoodToSectionSource R V r := by
  apply (cancel_mono (neighborhoodSourceOpen R V r).ι).mp
  simp only [commonNeighborhoodSectionProjection, Category.assoc,
    neighborhoodRestrictedProjection, morphismRestrict_ι,
    Scheme.isoOfEq_hom_ι_assoc, commonNeighborhoodToSectionAmbient_ι_assoc,
    commonNeighborhoodToSectionSource_ι, commonNeighborhoodToGraphAmbient, pullback.lift_fst]

@[reassoc] lemma commonNeighborhoodRetainedToSection_projection :
    commonNeighborhoodRetainedToSection R V r ≫
      (neighborhoodRetainedInclusion R V ∣_ neighborhoodSectionOpen R V r) ≫
        commonNeighborhoodSectionProjection R V r =
      pullback.fst (commonNeighborhoodProjection R V r)
        ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _) ≫
          commonNeighborhoodToSectionSource R V r := by
  rw [← Category.assoc, commonNeighborhoodRetainedToSection_inclusion, Category.assoc,
    commonNeighborhoodToSectionAmbient_projection, ← Category.assoc,
    commonNeighborhoodRetainedInclusion_fst]

@[reassoc (attr := simp)] lemma commonNeighborhoodRetainedToSection_target :
    commonNeighborhoodRetainedToSection R V r ≫
      (neighborhoodRetainedInclusion R V ⁻¹ᵁ neighborhoodSectionOpen R V r).ι ≫
        pullback.snd (neighborhoodProjection R V)
          ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _) =
      pullback.snd (commonNeighborhoodProjection R V r)
        ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _) := by
  rw [commonNeighborhoodRetainedToSection_ι_assoc, commonNeighborhoodRetainedToGraph_snd]
lemma commonNeighborhoodSectionProjection_isPullback :
    IsPullback (neighborhoodSectionOpen R V r).ι
      (commonNeighborhoodSectionProjection R V r)
      (pullback.fst (neighborhoodProjection R V) (ProjectiveSpace.toSpec R _))
      (neighborhoodSourceOpen R V r).ι := by
  exact (isPullback_morphismRestrict
    (pullback.fst (neighborhoodProjection R V) (ProjectiveSpace.toSpec R _))
    (neighborhoodSourceOpen R V r)).flip.of_iso'
      ((neighborhoodGraphAmbient R V).isoOfEq (neighborhoodSerreOpen_eq_compact R V r))
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp only [Iso.refl_hom, Category.comp_id]) (by simp) (by simp)

lemma commonNeighborhoodToSectionAmbient_source_isPullback :
    IsPullback (commonNeighborhoodToSectionAmbient R V r)
      (pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _))
      (commonNeighborhoodSectionProjection R V r)
      (commonNeighborhoodToSectionSource R V r) := by
  apply IsPullback.of_right (h₁₂ := (neighborhoodSectionOpen R V r).ι)
    (h₂₂ := (neighborhoodSourceOpen R V r).ι)
  · simpa only [commonNeighborhoodToSectionAmbient_ι, commonNeighborhoodToSectionSource_ι]
      using commonNeighborhoodToGraphAmbient_isPullback R V r
  · exact commonNeighborhoodToSectionAmbient_projection R V r
  · exact commonNeighborhoodSectionProjection_isPullback R V r

/-- Whole retained source square for the literal lambda factor span. -/
lemma commonNeighborhoodRetainedToSection_source_isPullback :
    IsPullback (commonNeighborhoodRetainedToSection R V r)
      (pullback.fst (commonNeighborhoodProjection R V r)
        ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _))
      ((neighborhoodRetainedInclusion R V ∣_ neighborhoodSectionOpen R V r) ≫
        commonNeighborhoodSectionProjection R V r)
      (commonNeighborhoodToSectionSource R V r) := by
  simpa only [commonNeighborhoodRetainedInclusion_fst] using
    (commonNeighborhoodRetainedToSection_isPullback R V r).paste_vert
      (commonNeighborhoodToSectionAmbient_source_isPullback R V r)
end AlgebraicGeometry.RelativeProjectiveLine
