module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Graph.Geometry
/-! # Prescribed graph-bundle trivialization for the actual relative zero neighborhood -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens)
variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)

/-- The whole zero section lifted to the unchanged open neighborhood. -/
def neighborhoodZero : Spec (.of R) ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))
    (by simpa only [Scheme.Opens.range_ι] using hV)

@[reassoc (attr := simp)]
lemma neighborhoodZero_ι : neighborhoodZero R V hV ≫ V.ι =
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
lemma neighborhoodZero_inclusion : neighborhoodZero R V hV ≫ neighborhoodInclusion R V =
    zeroSection R := by simp [neighborhoodInclusion, zeroSection]

lemma neighborhoodZero_isPullback :
    IsPullback (neighborhoodZero R V hV) (𝟙 _) V.ι
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) :=
  IsOpenImmersion.isPullback_lift_id _ _ _

lemma neighborhoodInclusion_disjoint :
    Disjoint (Set.range (neighborhoodInclusion R V))
      (Set.range (neighborhoodBoundaryInclusion R V)) := by
  rw [range_neighborhoodBoundaryInclusion]
  apply Set.disjoint_left.mpr
  rintro x ⟨y, rfl⟩ hx
  exact hx ⟨y.val, y.property, rfl⟩

/-- The ideal module of the original neighborhood graph. -/
abbrev neighborhoodGraphIdeal := Scheme.Hom.idealModule
  (Scheme.Hom.compactificationGraph (ProjectiveSpace.toSpec R _) (neighborhoodInclusion R V))

/-- The rank-one ideal bundle of the original neighborhood graph. -/
def neighborhoodGraphLine : LineBundle (neighborhoodGraphAmbient R V) :=
  ⟨neighborhoodGraphIdeal R V, neighborhoodGraph_ideal_rankOne R V⟩

/-- The dual line bundle of the original neighborhood graph ideal. -/
abbrev neighborhoodGraphDivisor := dualLineBundle _ (neighborhoodGraphLine R V)

/-- The coproduct of the missing-boundary and whole-zero boundary sources. -/
abbrev neighborhoodGraphBoundarySource :=
  pullback (pullback.snd (neighborhoodProjection R V) (ProjectiveSpace.toSpec R _))
    (neighborhoodBoundaryInclusion R V) ⨿
  pullback (neighborhoodProjection R V) (neighborhoodZero R V hV ≫
    neighborhoodInclusion R V ≫ ProjectiveSpace.toSpec R _)

/-- The full boundary map for the original neighborhood graph. -/
abbrev neighborhoodGraphBoundaryMap := Scheme.Hom.fullBoundaryProductMap
  (ProjectiveSpace.toSpec R _) (neighborhoodInclusion R V)
  (neighborhoodBoundaryInclusion R V) (neighborhoodZero R V hV)

lemma neighborhoodGraphBoundary_closed :
    IsClosedImmersion (neighborhoodGraphBoundaryMap R V hV) := by
  have : IsClosedImmersion (neighborhoodZero R V hV ≫ neighborhoodInclusion R V) := by
    rw [neighborhoodZero_inclusion]
    infer_instance
  exact Scheme.Hom.fullBoundaryProduct_isClosedImmersion _ _ _ _
    (neighborhoodInclusion_disjoint R V)

lemma neighborhoodGraphBoundary_finite : IsFinite (neighborhoodGraphBoundaryMap R V hV ≫
    pullback.fst (neighborhoodProjection R V) (ProjectiveSpace.toSpec R _)) := by
  have := neighborhoodBoundary_finite R V hV
  have : IsFinite (neighborhoodZero R V hV ≫ neighborhoodInclusion R V ≫
      ProjectiveSpace.toSpec R _) := by
    rw [← Category.assoc, neighborhoodZero_inclusion, zeroSection_toSpec]
    infer_instance
  exact Scheme.Hom.fullBoundaryProduct_finite _ _ _ _

/-- The full prescribed trivialization is constructed from canonical missing-boundary
unit and the original affine coordinate graph. -/
def neighborhoodGraphBoundaryIso :
    (Scheme.Modules.pullback (neighborhoodGraphBoundaryMap R V hV)).obj
      (neighborhoodGraphDivisor R V).val ≅
        SheafOfModules.unit (neighborhoodGraphBoundarySource R V hV).ringCatSheaf := by
  have := neighborhoodGraph_affineOpen_smooth R V
  exact Classical.choose (Scheme.Hom.exists_fullBoundaryDivisorIso R R
    (Polynomial.evalRingHom 0) (ProjectiveSpace.toSpec R _) (neighborhoodInclusion R V)
    V.ι (by simp [neighborhoodInclusion, Scheme.Hom.boundaryLineProjection, chart_toSpec])
    (neighborhoodZero R V hV) (neighborhoodZero_ι R V hV) (neighborhoodZero_isPullback R V hV)
    (neighborhoodBoundaryInclusion R V) (neighborhoodInclusion_disjoint R V)
    (neighborhoodAffineInclusion R V).opensRange (neighborhoodGraph_mem_affine R V))
/-- The canonical graph-divisor trivialization on the missing boundary. -/
def neighborhoodMissingDivisorIso :=
  Scheme.Hom.infinityBoundaryDivisorIso (ProjectiveSpace.toSpec R _)
    (neighborhoodInclusion R V) (neighborhoodBoundaryInclusion R V)
    (neighborhoodInclusion_disjoint R V) (neighborhoodGraph_ideal_rankOne R V)

lemma neighborhoodProjection_eq : neighborhoodInclusion R V ≫ ProjectiveSpace.toSpec R _ =
    V.ι ≫ Scheme.Hom.boundaryLineProjection R := by
  simp [neighborhoodInclusion, Scheme.Hom.boundaryLineProjection, chart_toSpec]

/-- The coordinate graph-divisor trivialization on the whole zero section. -/
def neighborhoodZeroDivisorIso :=
  Scheme.Hom.compactificationBoundaryDivisorIso R R (Polynomial.evalRingHom 0)
    (ProjectiveSpace.toSpec R _) (neighborhoodInclusion R V) V.ι
    (neighborhoodProjection_eq R V) (neighborhoodZero R V hV)
    (neighborhoodZero_ι R V hV) (neighborhoodZero_isPullback R V hV)
    (neighborhoodGraph_ideal_rankOne R V)

/-- Literal canonical value on the missing-neighborhood component. -/
lemma neighborhoodGraphBoundaryIso_missing :
    (Scheme.Modules.restrictFunctor (coprod.inl :
      pullback (pullback.snd (neighborhoodProjection R V) (ProjectiveSpace.toSpec R _))
        (neighborhoodBoundaryInclusion R V) ⟶ neighborhoodGraphBoundarySource R V hV)).map
      (neighborhoodGraphBoundaryIso R V hV).hom ≫ (Scheme.Modules.restrictUnitIso _).hom =
    (Scheme.Modules.coprodPullbackRestrictLeft
      (Scheme.Hom.infinityProductMap (ProjectiveSpace.toSpec R _) (neighborhoodInclusion R V)
        (neighborhoodBoundaryInclusion R V))
      (Scheme.Hom.graphBoundaryRestriction (ProjectiveSpace.toSpec R _)
        (neighborhoodInclusion R V) (neighborhoodZero R V hV))).hom.app
      (neighborhoodGraphDivisor R V).val ≫ (neighborhoodMissingDivisorIso R V).hom := by
  have := neighborhoodGraph_affineOpen_smooth R V
  exact (Classical.choose_spec (Scheme.Hom.exists_fullBoundaryDivisorIso R R
    (Polynomial.evalRingHom 0) (ProjectiveSpace.toSpec R _) (neighborhoodInclusion R V)
    V.ι (neighborhoodProjection_eq R V)
    (neighborhoodZero R V hV) (neighborhoodZero_ι R V hV) (neighborhoodZero_isPullback R V hV)
    (neighborhoodBoundaryInclusion R V) (neighborhoodInclusion_disjoint R V)
    (neighborhoodAffineInclusion R V).opensRange (neighborhoodGraph_mem_affine R V))).1

/-- Literal coordinate value on the whole original zero section. -/
lemma neighborhoodGraphBoundaryIso_zero :
    (Scheme.Modules.restrictFunctor (coprod.inr :
      pullback (neighborhoodProjection R V) (neighborhoodZero R V hV ≫
        neighborhoodInclusion R V ≫ ProjectiveSpace.toSpec R _) ⟶
          neighborhoodGraphBoundarySource R V hV)).map
      (neighborhoodGraphBoundaryIso R V hV).hom ≫ (Scheme.Modules.restrictUnitIso _).hom =
    (Scheme.Modules.coprodPullbackRestrictRight
      (Scheme.Hom.infinityProductMap (ProjectiveSpace.toSpec R _) (neighborhoodInclusion R V)
        (neighborhoodBoundaryInclusion R V))
      (Scheme.Hom.graphBoundaryRestriction (ProjectiveSpace.toSpec R _)
        (neighborhoodInclusion R V) (neighborhoodZero R V hV))).hom.app
      (neighborhoodGraphDivisor R V).val ≫ (neighborhoodZeroDivisorIso R V hV).hom := by
  have := neighborhoodGraph_affineOpen_smooth R V
  exact (Classical.choose_spec (Scheme.Hom.exists_fullBoundaryDivisorIso R R
    (Polynomial.evalRingHom 0) (ProjectiveSpace.toSpec R _) (neighborhoodInclusion R V)
    V.ι (neighborhoodProjection_eq R V)
    (neighborhoodZero R V hV) (neighborhoodZero_ι R V hV) (neighborhoodZero_isPullback R V hV)
    (neighborhoodBoundaryInclusion R V) (neighborhoodInclusion_disjoint R V)
    (neighborhoodAffineInclusion R V).opensRange (neighborhoodGraph_mem_affine R V))).2
end AlgebraicGeometry.RelativeProjectiveLine
