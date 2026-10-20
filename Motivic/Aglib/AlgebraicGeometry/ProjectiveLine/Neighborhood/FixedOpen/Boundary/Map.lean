module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.FixedOpen.Boundary.Basic
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.DisjointClosedImmersion
/-! # The actual closed whole boundary on the fixed punctured source -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] (r : R)

/-- The map into the fixed ambient scheme induced by base change of `g`. -/
def fixedPsiProductBoundaryMap {D : Scheme.{u}}
    (g : D ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) :
    pullback (fixedPsiProjection R r) (g ≫ ProjectiveSpace.toSpec R _) ⟶
      fixedPsiAmbient R r :=
  (IsPullback.of_hasPullback (fixedPsiProjection R r)
    (ProjectiveSpace.toSpec R _)).flip.lift (pullback.snd _ _ ≫ g) (pullback.fst _ _)
    (by rw [Category.assoc]; exact pullback.condition.symm)

lemma fixedPsiProductBoundaryMap_isPullback {D : Scheme.{u}}
    (g : D ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) :
    IsPullback (pullback.snd _ _) (fixedPsiProductBoundaryMap R r g) g
      (pullback.snd (fixedPsiProjection R r) (ProjectiveSpace.toSpec R _)) :=
  (IsPullback.of_hasPullback (fixedPsiProjection R r)
    (g ≫ ProjectiveSpace.toSpec R _)).flip.of_bot'
      (IsPullback.of_hasPullback (fixedPsiProjection R r)
        (ProjectiveSpace.toSpec R _)).flip

variable (V : (Spec (.of (Polynomial R))).Opens)

/-- The inclusion of the pulled-back missing boundary into the fixed ambient scheme. -/
def fixedPsiMissingMap : fixedPsiMissing R V r ⟶ fixedPsiAmbient R r :=
  fixedPsiProductBoundaryMap R r (neighborhoodBoundaryInclusion R V)

/-- The map of the pulled-back zero component into the fixed ambient scheme. -/
def fixedPsiZeroMap : fixedPsiZero R r ⟶ fixedPsiAmbient R r :=
  (IsPullback.of_hasPullback (fixedPsiProjection R r)
    (ProjectiveSpace.toSpec R _)).flip.lift (pullback.snd _ _ ≫ zeroSection R)
      (pullback.fst _ _) (by
    rw [Category.assoc]
    simpa only [zeroSection, Category.assoc, chart_toSpec,
      Scheme.Hom.boundaryCoordinateMap, Scheme.Hom.boundaryLineProjection] using
      (pullback.condition (f := fixedPsiProjection R r)
        (g := Scheme.Hom.boundaryCoordinateMap R R (Polynomial.evalRingHom 0) ≫
          Scheme.Hom.boundaryLineProjection R)).symm)

@[reassoc (attr := simp)] lemma fixedPsiMissingMap_snd :
    fixedPsiMissingMap R r V ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ neighborhoodBoundaryInclusion R V :=
  (IsPullback.of_hasPullback _ _).flip.lift_fst _ _ _

@[reassoc (attr := simp)] lemma fixedPsiZeroMap_snd :
    fixedPsiZeroMap R r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ zeroSection R :=
  (IsPullback.of_hasPullback _ _).flip.lift_fst _ _ _

lemma fixedPsiZeroMap_isPullback :
    IsPullback (pullback.snd _ _) (fixedPsiZeroMap R r) (zeroSection R)
      (pullback.snd (fixedPsiProjection R r) (ProjectiveSpace.toSpec R _)) := by
  have h : zeroSection R ≫ ProjectiveSpace.toSpec R _ =
      Scheme.Hom.boundaryCoordinateMap R R (Polynomial.evalRingHom 0) ≫
        Scheme.Hom.boundaryLineProjection R := by
    simp only [zeroSection, Category.assoc, chart_toSpec,
      Scheme.Hom.boundaryCoordinateMap, Scheme.Hom.boundaryLineProjection]
  have H : IsPullback (pullback.snd (fixedPsiProjection R r)
      (Scheme.Hom.boundaryCoordinateMap R R (Polynomial.evalRingHom 0) ≫
        Scheme.Hom.boundaryLineProjection R)) (pullback.fst _ _)
      (zeroSection R ≫ ProjectiveSpace.toSpec R _) (fixedPsiProjection R r) := by
    rw [h]; exact (IsPullback.of_hasPullback _ _).flip
  exact H.of_bot' (IsPullback.of_hasPullback (fixedPsiProjection R r)
    (ProjectiveSpace.toSpec R _)).flip

/-- The map of the whole fixed boundary into the ambient scheme, defined on both components. -/
def fixedPsiBoundaryMap : fixedPsiBoundary R V r ⟶ fixedPsiAmbient R r :=
  coprod.desc (fixedPsiMissingMap R r V) (fixedPsiZeroMap R r)

/-- Project both fixed boundary components to their corresponding original components. -/
def fixedPsiBoundaryToOriginal : fixedPsiBoundary R V r ⟶
    neighborhoodBoundary R V ⨿ Spec (.of R) :=
  coprod.map (pullback.snd _ _) (pullback.snd _ _)

@[reassoc] lemma fixedPsiBoundaryToOriginal_fac :
    fixedPsiBoundaryMap R r V ≫ pullback.snd _ _ =
      fixedPsiBoundaryToOriginal R r V ≫ fullNeighborhoodBoundaryMap R V := by
  apply coprod.hom_ext <;>
    simp [fixedPsiBoundaryMap, fixedPsiBoundaryToOriginal, fullNeighborhoodBoundaryMap]

lemma fixedPsiBoundary_closed
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V) :
    IsClosedImmersion (fixedPsiBoundaryMap R r V) := by
  have : IsClosedImmersion (fixedPsiMissingMap R r V) :=
    MorphismProperty.of_isPullback
      (fixedPsiProductBoundaryMap_isPullback R r (neighborhoodBoundaryInclusion R V)) inferInstance
  have : IsClosedImmersion (fixedPsiZeroMap R r) :=
    MorphismProperty.of_isPullback (fixedPsiZeroMap_isPullback R r) inferInstance
  apply isClosedImmersion_coprod_desc
  apply Set.disjoint_left.mpr
  rintro x ⟨v, rfl⟩ ⟨w, hw⟩
  have h1 := congrArg (fun f => f v) (fixedPsiMissingMap_snd R r V)
  have h2 := congrArg (fun f => f w) (fixedPsiZeroMap_snd R r)
  have h3 := congrArg (fun t => (pullback.snd (fixedPsiProjection R r)
    (ProjectiveSpace.toSpec R _)) t) hw
  exact Set.disjoint_iff_forall_ne.mp (neighborhoodBoundary_disjoint_zero R V hV)
    ⟨_, rfl⟩ ⟨_, rfl⟩ (h1.symm.trans (h3.symm.trans h2))
end AlgebraicGeometry.RelativeProjectiveLine
