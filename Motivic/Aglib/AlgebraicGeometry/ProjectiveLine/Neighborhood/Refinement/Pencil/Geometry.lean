module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Boundary.Maps
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Retained.Geometry
/-! # The actual retained relative curve and full boundary for the common pencil -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens) (r : R)

lemma commonNeighborhoodSource_affine [IsAffine V.toScheme] :
    IsAffine (commonNeighborhoodSource R V r).toScheme :=
  (show IsAffineOpen V from ‹IsAffine V.toScheme›).inf
    (show IsAffineOpen (fixedPsiSource R r) from
      inferInstanceAs (IsAffine (fixedPsiSource R r).toScheme))

lemma commonNeighborhoodProjection_proper : IsProper
    (pullback.fst (commonNeighborhoodProjection R V r)
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) := inferInstance

lemma commonNeighborhoodMissingInclusion_isPullback :
    IsPullback (pullback.snd _ _) (commonNeighborhoodMissingInclusion R V r)
      (neighborhoodBoundaryInclusion R V)
      (pullback.snd (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _)) := by
  apply IsPullback.of_bot (v₂₁ := pullback.fst _ _)
    (v₂₂ := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
  · simpa only [commonNeighborhoodMissingInclusion, pullback.lift_fst] using
      (IsPullback.of_hasPullback (commonNeighborhoodProjection R V r)
        (neighborhoodBoundaryInclusion R V ≫ ProjectiveSpace.toSpec R _)).flip
  · simp [commonNeighborhoodMissingInclusion]
  · exact (IsPullback.of_hasPullback _ _).flip

lemma commonNeighborhoodZeroInclusion_isPullback :
    IsPullback (pullback.snd _ _) (commonNeighborhoodZeroInclusion R V r)
      (zeroSection R)
      (pullback.snd (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _)) := by
  apply IsPullback.of_bot (v₂₁ := pullback.fst _ _)
    (v₂₂ := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
  · have h : zeroSection R ≫ ProjectiveSpace.toSpec R _ =
        Scheme.Hom.boundaryCoordinateMap R R (Polynomial.evalRingHom 0) ≫
          Scheme.Hom.boundaryLineProjection R := by
      simp only [zeroSection, Category.assoc, chart_toSpec,
        Scheme.Hom.boundaryCoordinateMap, Scheme.Hom.boundaryLineProjection]
    simpa only [commonNeighborhoodZeroInclusion, pullback.lift_fst, h] using
      (IsPullback.of_hasPullback (commonNeighborhoodProjection R V r)
        (Scheme.Hom.boundaryCoordinateMap R R (Polynomial.evalRingHom 0) ≫
          Scheme.Hom.boundaryLineProjection R)).flip
  · simp [commonNeighborhoodZeroInclusion]
  · exact (IsPullback.of_hasPullback _ _).flip

lemma commonNeighborhoodBoundary_closed
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V) :
    IsClosedImmersion (commonNeighborhoodBoundaryMap R V r) := by
  have : IsClosedImmersion (commonNeighborhoodMissingInclusion R V r) :=
    MorphismProperty.of_isPullback (commonNeighborhoodMissingInclusion_isPullback R V r)
      inferInstance
  have : IsClosedImmersion (commonNeighborhoodZeroInclusion R V r) :=
    MorphismProperty.of_isPullback (commonNeighborhoodZeroInclusion_isPullback R V r)
      inferInstance
  apply isClosedImmersion_coprod_desc
  apply Set.disjoint_left.mpr
  rintro x ⟨v, rfl⟩ ⟨w, hw⟩
  have h1 := congrArg (fun f => f v)
    (pullback.lift_snd (f := commonNeighborhoodProjection R V r)
      (g := ProjectiveSpace.toSpec R _) (pullback.fst _ _)
      (pullback.snd _ _ ≫ neighborhoodBoundaryInclusion R V)
      (by rw [Category.assoc]; exact pullback.condition))
  have h2 := congrArg (fun f => f w)
    (commonNeighborhoodZeroInclusion_isPullback R V r).w
  have h3 := congrArg (fun t => (pullback.snd (commonNeighborhoodProjection R V r)
    (ProjectiveSpace.toSpec R _)) t) hw
  exact Set.disjoint_iff_forall_ne.mp (neighborhoodBoundary_disjoint_zero R V hV)
    ⟨_, rfl⟩ ⟨_, rfl⟩ (h1.symm.trans (h3.symm.trans h2.symm))

/-- The common neighborhood curve restricted to the retained target open. -/
abbrev commonNeighborhoodRetainedCurve := pullback (commonNeighborhoodProjection R V r)
  ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))

/-- The inclusion of the retained common neighborhood curve into its ambient scheme. -/
def commonNeighborhoodRetainedInclusion : commonNeighborhoodRetainedCurve R V r ⟶
    commonNeighborhoodAmbient R V r :=
  (IsPullback.of_hasPullback (commonNeighborhoodProjection R V r)
    (ProjectiveSpace.toSpec R _)).flip.lift
    (pullback.snd _ _ ≫ (neighborhoodRetainedOpen R V).ι) (pullback.fst _ _)
    (by rw [Category.assoc]; exact pullback.condition.symm)

@[reassoc (attr := simp)] lemma commonNeighborhoodRetainedInclusion_fst :
    commonNeighborhoodRetainedInclusion R V r ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (IsPullback.of_hasPullback _ _).flip.lift_snd _ _ _

@[reassoc (attr := simp)] lemma commonNeighborhoodRetainedInclusion_snd :
    commonNeighborhoodRetainedInclusion R V r ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (neighborhoodRetainedOpen R V).ι :=
  (IsPullback.of_hasPullback _ _).flip.lift_fst _ _ _

lemma commonNeighborhoodRetainedInclusion_isPullback :
    IsPullback (pullback.snd _ _) (commonNeighborhoodRetainedInclusion R V r)
      (neighborhoodRetainedOpen R V).ι
      (pullback.snd (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _)) :=
  (IsPullback.of_hasPullback (commonNeighborhoodProjection R V r)
    ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _)).flip.of_bot'
      (IsPullback.of_hasPullback _ _).flip

instance : IsOpenImmersion (commonNeighborhoodRetainedInclusion R V r) :=
  MorphismProperty.of_isPullback (commonNeighborhoodRetainedInclusion_isPullback R V r)
    inferInstance

lemma commonNeighborhoodRetainedCurve_affine [IsAffine V.toScheme] :
    IsAffine (commonNeighborhoodRetainedCurve R V r) := by
  have := commonNeighborhoodSource_affine R V r
  have : IsAffine (neighborhoodRetainedOpen R V).toScheme :=
    neighborhoodRetained_isAffineOpen R V
  exact isAffine_of_isAffineHom (pullback.fst (commonNeighborhoodProjection R V r)
    ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _))

lemma commonNeighborhoodRetainedCurve_smooth : SmoothOfRelativeDimension 1
    (commonNeighborhoodRetainedInclusion R V r ≫
      pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _)) := by
  rw [commonNeighborhoodRetainedInclusion_fst]
  have := neighborhoodRetained_projection_smooth R V
  exact MorphismProperty.pullback_fst _ _ inferInstance

lemma commonNeighborhoodRetained_boundary_cover : ∀ x : commonNeighborhoodAmbient R V r,
    x ∈ Set.range (commonNeighborhoodRetainedInclusion R V r) ∨
      x ∈ Set.range (commonNeighborhoodBoundaryMap R V r) := by
  intro x
  let π := pullback.snd (commonNeighborhoodProjection R V r)
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
  by_cases hx : π x ∈ neighborhoodRetainedOpen R V
  · left
    obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
      (commonNeighborhoodRetainedInclusion_isPullback R V r).flip x ⟨π x, hx⟩ rfl
    exact ⟨w, hw⟩
  · right
    by_cases hv : π x ∈ projectiveNeighborhood R V
    · have hzero : π x ∈ Set.range (zeroSection R) := by
        rw [range_zeroSection]
        exact fun hc => hx ⟨hv, hc⟩
      obtain ⟨z, hz⟩ := hzero
      obtain ⟨w, _, hw⟩ := Scheme.exists_preimage_of_isPullback
        (commonNeighborhoodZeroInclusion_isPullback R V r) z x hz
      refine ⟨(coprod.inr : _ ⟶ commonNeighborhoodBoundary R V r) w, ?_⟩
      change ((coprod.inr : _ ⟶ commonNeighborhoodBoundary R V r) ≫
        commonNeighborhoodBoundaryMap R V r) w = x
      simpa only [commonNeighborhoodBoundaryMap, coprod.inr_desc] using hw
    · have hb : π x ∈ Set.range (neighborhoodBoundaryInclusion R V) := by
        rw [range_neighborhoodBoundaryInclusion]
        exact hv
      obtain ⟨z, hz⟩ := hb
      obtain ⟨w, _, hw⟩ := Scheme.exists_preimage_of_isPullback
        (commonNeighborhoodMissingInclusion_isPullback R V r) z x hz
      refine ⟨(coprod.inl : _ ⟶ commonNeighborhoodBoundary R V r) w, ?_⟩
      change ((coprod.inl : _ ⟶ commonNeighborhoodBoundary R V r) ≫
        commonNeighborhoodBoundaryMap R V r) w = x
      simpa only [commonNeighborhoodBoundaryMap, coprod.inl_desc] using hw
end AlgebraicGeometry.RelativeProjectiveLine
