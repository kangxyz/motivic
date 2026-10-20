module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Graph.Boundary
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.ProjectiveLine.CoordinateSection.Basic
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.SectionDualDivisor
/-! # The original punctured neighborhood is the retained affine relative curve -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens)

/-- The intersection of the projective neighborhood with the coordinate open indexed by one. -/
abbrev neighborhoodRetainedOpen := projectiveNeighborhood R V ⊓
  ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) ⟨1⟩

lemma neighborhoodRetained_complement :
    (neighborhoodRetainedOpen R V : Set (ProjectiveSpace R (ULift.{u} (Fin 2))))ᶜ =
      Set.range (neighborhoodBoundaryInclusion R V) ∪ Set.range (zeroSection R) := by
  rw [range_neighborhoodBoundaryInclusion, range_zeroSection]
  exact Set.compl_inter _ _

lemma neighborhoodInclusion_opensRange :
    (neighborhoodInclusion R V).opensRange = projectiveNeighborhood R V := by
  simp only [neighborhoodInclusion, Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
    projectiveNeighborhood]

lemma neighborhoodRetained_isAffineOpen [IsAffine V.toScheme] :
    IsAffineOpen (neighborhoodRetainedOpen R V) := by
  have h : IsAffineOpen (projectiveNeighborhood R V) := by
    rw [← neighborhoodInclusion_opensRange]
    exact isAffineOpen_opensRange _
  exact h.inf (ProjectiveSpace.isAffineOpen_coordinateOpen R (ULift.{u} (Fin 2)) ⟨1⟩)

lemma neighborhoodRetained_le_chart : neighborhoodRetainedOpen R V ≤
    ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) ⟨0⟩ := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := hx.1
  rw [← chart_opensRange]
  exact ⟨y, rfl⟩

lemma neighborhoodRetained_projection_smooth : SmoothOfRelativeDimension 1
    ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  let i := (ProjectiveSpace R (ULift.{u} (Fin 2))).homOfLE (neighborhoodRetained_le_chart R V)
  have hi : i ≫ (ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) ⟨0⟩).ι =
      (neighborhoodRetainedOpen R V).ι := Scheme.homOfLE_ι _ _
  rw [← hi, Category.assoc]
  have := coordinateOpen_smooth_one R ⟨0⟩
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

/-- The retained open pulled back along the neighborhood projection. -/
abbrev neighborhoodRetainedCurve := pullback (neighborhoodProjection R V)
  ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))

/-- The map from the retained curve into the graph ambient projective line. -/
def neighborhoodRetainedInclusion : neighborhoodRetainedCurve R V ⟶
    neighborhoodGraphAmbient R V :=
  (IsPullback.of_hasPullback (neighborhoodProjection R V)
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))).flip.lift
      (pullback.snd _ _ ≫ (neighborhoodRetainedOpen R V).ι) (pullback.fst _ _)
      (by rw [Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
lemma neighborhoodRetainedInclusion_fst : neighborhoodRetainedInclusion R V ≫
    pullback.fst _ _ = pullback.fst _ _ :=
  (IsPullback.of_hasPullback _ _).flip.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma neighborhoodRetainedInclusion_snd : neighborhoodRetainedInclusion R V ≫
    pullback.snd _ _ = pullback.snd _ _ ≫ (neighborhoodRetainedOpen R V).ι :=
  (IsPullback.of_hasPullback _ _).flip.lift_fst _ _ _

lemma neighborhoodRetainedInclusion_isPullback :
    IsPullback (pullback.snd _ _) (neighborhoodRetainedInclusion R V)
      (neighborhoodRetainedOpen R V).ι
      (pullback.snd (neighborhoodProjection R V) (ProjectiveSpace.toSpec R _)) :=
  (IsPullback.of_hasPullback (neighborhoodProjection R V)
    ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _)).flip.of_bot'
      (IsPullback.of_hasPullback _ _).flip

instance : IsOpenImmersion (neighborhoodRetainedInclusion R V) :=
  MorphismProperty.of_isPullback (neighborhoodRetainedInclusion_isPullback R V) inferInstance

lemma neighborhoodRetainedCurve_affine [IsAffine V.toScheme] :
    IsAffine (neighborhoodRetainedCurve R V) := by
  have : IsAffine (neighborhoodRetainedOpen R V).toScheme :=
    neighborhoodRetained_isAffineOpen R V
  exact isAffine_of_isAffineHom (pullback.fst (neighborhoodProjection R V)
    ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _))

lemma neighborhoodRetainedCurve_smooth : SmoothOfRelativeDimension 1
    (neighborhoodRetainedInclusion R V ≫
      pullback.fst (neighborhoodProjection R V) (ProjectiveSpace.toSpec R _)) := by
  rw [neighborhoodRetainedInclusion_fst]
  have := neighborhoodRetained_projection_smooth R V
  exact MorphismProperty.pullback_fst _ _ inferInstance

/-- The retained target is exactly the original punctured neighborhood; its complement
is covered by the whole prescribed missing-neighborhood plus zero boundary. -/
lemma neighborhoodRetained_boundary_cover
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V) :
    ∀ x : neighborhoodGraphAmbient R V,
      x ∈ Set.range (neighborhoodRetainedInclusion R V) ∨
        x ∈ Set.range (neighborhoodGraphBoundaryMap R V hV) := by
  intro x
  let π := pullback.snd (neighborhoodProjection R V)
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
  by_cases hx : π x ∈ neighborhoodRetainedOpen R V
  · left
    obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
      (neighborhoodRetainedInclusion_isPullback R V).flip x ⟨π x, hx⟩ rfl
    exact ⟨w, hw⟩
  · right
    by_cases hv : π x ∈ projectiveNeighborhood R V
    · have hzero : π x ∈ Set.range (zeroSection R) := by
        rw [range_zeroSection]
        exact fun hc => hx ⟨hv, hc⟩
      obtain ⟨z, hz⟩ := hzero
      have H := Scheme.Hom.graphBoundaryRestriction_isPullback
        (ProjectiveSpace.toSpec R _) (neighborhoodInclusion R V) (neighborhoodZero R V hV)
      have he : π x = (neighborhoodZero R V hV ≫ neighborhoodInclusion R V) z := by
        rw [neighborhoodZero_inclusion]
        exact hz.symm
      obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback H x z he
      refine ⟨(coprod.inr : _ ⟶ neighborhoodGraphBoundarySource R V hV) w, ?_⟩
      change ((coprod.inr : _ ⟶ neighborhoodGraphBoundarySource R V hV) ≫
        neighborhoodGraphBoundaryMap R V hV) w = x
      simpa only [neighborhoodGraphBoundaryMap, Scheme.Hom.fullBoundaryProductMap,
        coprod.inr_desc] using hw
    · have hb : π x ∈ Set.range (neighborhoodBoundaryInclusion R V) := by
        rw [range_neighborhoodBoundaryInclusion]
        exact hv
      have hx' : x ∈ Set.range (Scheme.Hom.infinityProductMap (ProjectiveSpace.toSpec R _)
          (neighborhoodInclusion R V) (neighborhoodBoundaryInclusion R V)) := by
        change x ∈ Set.range (pullback.fst π (neighborhoodBoundaryInclusion R V))
        rw [Scheme.Pullback.range_fst]
        exact hb
      obtain ⟨w, hw⟩ := hx'
      refine ⟨(coprod.inl : _ ⟶ neighborhoodGraphBoundarySource R V hV) w, ?_⟩
      change ((coprod.inl : _ ⟶ neighborhoodGraphBoundarySource R V hV) ≫
        neighborhoodGraphBoundaryMap R V hV) w = x
      simpa only [neighborhoodGraphBoundaryMap, Scheme.Hom.fullBoundaryProductMap,
        coprod.inl_desc] using hw

end AlgebraicGeometry.RelativeProjectiveLine
