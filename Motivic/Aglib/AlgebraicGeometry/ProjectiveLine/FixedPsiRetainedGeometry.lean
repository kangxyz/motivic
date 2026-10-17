module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.FixedPsiBoundaryMap
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodRetainedGeometry
/-! # The unchanged punctured-neighborhood target for the fixed psi source -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] (r : R)
  (V : (Spec (.of (Polynomial R))).Opens)

abbrev fixedPsiRetainedCurve := pullback (fixedPsiProjection R r)
  ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))

def fixedPsiRetainedInclusion : fixedPsiRetainedCurve R r V ⟶ fixedPsiAmbient R r :=
  fixedPsiProductBoundaryMap R r (neighborhoodRetainedOpen R V).ι

@[reassoc (attr := simp)] lemma fixedPsiRetainedInclusion_fst :
    fixedPsiRetainedInclusion R r V ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (IsPullback.of_hasPullback _ _).flip.lift_snd _ _ _

lemma fixedPsiRetainedInclusion_isPullback :
    IsPullback (pullback.snd _ _) (fixedPsiRetainedInclusion R r V)
      (neighborhoodRetainedOpen R V).ι
      (pullback.snd (fixedPsiProjection R r) (ProjectiveSpace.toSpec R _)) :=
  fixedPsiProductBoundaryMap_isPullback R r _

instance : IsOpenImmersion (fixedPsiRetainedInclusion R r V) :=
  MorphismProperty.of_isPullback (fixedPsiRetainedInclusion_isPullback R r V) inferInstance

lemma fixedPsiRetainedCurve_affine [IsAffine V.toScheme] :
    IsAffine (fixedPsiRetainedCurve R r V) := by
  have : IsAffine (neighborhoodRetainedOpen R V).toScheme :=
    neighborhoodRetained_isAffineOpen R V
  exact isAffine_of_isAffineHom (pullback.fst (fixedPsiProjection R r)
    ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _))

lemma fixedPsiRetainedCurve_smooth : SmoothOfRelativeDimension 1
    (fixedPsiRetainedInclusion R r V ≫
      pullback.fst (fixedPsiProjection R r) (ProjectiveSpace.toSpec R _)) := by
  rw [fixedPsiRetainedInclusion_fst]
  have := neighborhoodRetained_projection_smooth R V
  exact MorphismProperty.pullback_fst _ _ inferInstance

lemma fixedPsiRetained_boundary_cover : ∀ x : fixedPsiAmbient R r,
    x ∈ Set.range (fixedPsiRetainedInclusion R r V) ∨
      x ∈ Set.range (fixedPsiBoundaryMap R r V) := by
  intro x
  let π := pullback.snd (fixedPsiProjection R r)
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
  by_cases hx : π x ∈ neighborhoodRetainedOpen R V
  · left
    obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
      (fixedPsiRetainedInclusion_isPullback R r V).flip x ⟨π x, hx⟩ rfl
    exact ⟨w, hw⟩
  · right
    by_cases hv : π x ∈ projectiveNeighborhood R V
    · have hzero : π x ∈ Set.range (zeroSection R) := by
        rw [range_zeroSection]
        exact fun hc => hx ⟨hv, hc⟩
      obtain ⟨z, hz⟩ := hzero
      obtain ⟨w, _, hw⟩ := Scheme.exists_preimage_of_isPullback
        (fixedPsiZeroMap_isPullback R r) z x hz
      refine ⟨(coprod.inr : _ ⟶ fixedPsiBoundary R V r) w, ?_⟩
      change ((coprod.inr : _ ⟶ fixedPsiBoundary R V r) ≫ fixedPsiBoundaryMap R r V) w = x
      simpa only [fixedPsiBoundaryMap, coprod.inr_desc] using hw
    · have hb : π x ∈ Set.range (neighborhoodBoundaryInclusion R V) := by
        rw [range_neighborhoodBoundaryInclusion]
        exact hv
      obtain ⟨z, hz⟩ := hb
      obtain ⟨w, _, hw⟩ := Scheme.exists_preimage_of_isPullback
        (fixedPsiProductBoundaryMap_isPullback R r (neighborhoodBoundaryInclusion R V)) z x hz
      refine ⟨(coprod.inl : _ ⟶ fixedPsiBoundary R V r) w, ?_⟩
      change ((coprod.inl : _ ⟶ fixedPsiBoundary R V r) ≫ fixedPsiBoundaryMap R r V) w = x
      simpa only [fixedPsiBoundaryMap, coprod.inl_desc, fixedPsiMissingMap] using hw
end AlgebraicGeometry.RelativeProjectiveLine
