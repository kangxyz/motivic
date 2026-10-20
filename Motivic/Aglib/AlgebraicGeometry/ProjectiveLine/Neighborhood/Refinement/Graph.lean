module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Cartesian
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Retained.Geometry
/-! # The original common diagonal and its unchanged punctured target -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens) (r : R)

/-- The target map from the common neighborhood source to the projective line. -/
def commonNeighborhoodTargetMap : (commonNeighborhoodSource R V r).toScheme ⟶
    ProjectiveSpace R (ULift.{u} (Fin 2)) :=
  (commonNeighborhoodSource R V r).ι ≫ chart R ⟨0⟩

lemma commonNeighborhoodTargetMap_eq : commonNeighborhoodTargetMap R V r =
    commonNeighborhoodToV R V r ≫ neighborhoodInclusion R V := by
  simp only [commonNeighborhoodTargetMap, neighborhoodInclusion, ← Category.assoc,
    commonNeighborhoodToV_ι]

lemma commonNeighborhoodTargetMap_mem (x : (commonNeighborhoodSource R V r).toScheme) :
    commonNeighborhoodTargetMap R V r x ∈ neighborhoodRetainedOpen R V := by
  change chart R ⟨0⟩ x.val ∈ (chart R ⟨0⟩ ''ᵁ V) ⊓
    ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) ⟨1⟩
  refine ⟨⟨x.val, x.property.1, rfl⟩, ?_⟩
  change x.val ∈ chart R ⟨0⟩ ⁻¹ᵁ ProjectiveSpace.coordinateOpen R _ ⟨1⟩
  rw [chart_preimage_other R ⟨0⟩ ⟨1⟩ (by decide)]
  have hx := x.property.2
  rw [fixedPsiSource_eq] at hx
  exact hx.1

/-- The target map lifted to the retained open of the projective line. -/
def commonNeighborhoodRetainedTargetMap : (commonNeighborhoodSource R V r).toScheme ⟶
    (neighborhoodRetainedOpen R V).toScheme :=
  IsOpenImmersion.lift (neighborhoodRetainedOpen R V).ι (commonNeighborhoodTargetMap R V r) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact commonNeighborhoodTargetMap_mem R V r x)

@[reassoc (attr := simp)] lemma commonNeighborhoodRetainedTargetMap_ι :
    commonNeighborhoodRetainedTargetMap R V r ≫ (neighborhoodRetainedOpen R V).ι =
      commonNeighborhoodTargetMap R V r := IsOpenImmersion.lift_fac _ _ _

/-- The graph of the common neighborhood target map. -/
def commonNeighborhoodGraph : (commonNeighborhoodSource R V r).toScheme ⟶
    commonNeighborhoodAmbient R V r :=
  pullback.lift (𝟙 _) (commonNeighborhoodTargetMap R V r) (by
    simp only [commonNeighborhoodTargetMap, commonNeighborhoodProjection, Category.id_comp,
      Category.assoc, chart_toSpec, Scheme.Hom.boundaryLineProjection])

@[reassoc (attr := simp)] lemma commonNeighborhoodGraph_fst :
    commonNeighborhoodGraph R V r ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
@[reassoc (attr := simp)] lemma commonNeighborhoodGraph_snd :
    commonNeighborhoodGraph R V r ≫ pullback.snd _ _ = commonNeighborhoodTargetMap R V r :=
  pullback.lift_snd _ _ _

lemma commonNeighborhoodGraph_isPullback :
    IsPullback (commonNeighborhoodToV R V r) (commonNeighborhoodGraph R V r)
      (Scheme.Hom.compactificationGraph (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
        (neighborhoodInclusion R V)) (commonNeighborhoodToGraphAmbient R V r) where
  w := by
    apply pullback.hom_ext <;>
      simp [commonNeighborhoodGraph, commonNeighborhoodToGraphAmbient,
        Scheme.Hom.compactificationGraph, Category.assoc, commonNeighborhoodTargetMap_eq]
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun t => by
    refine ⟨t.snd ≫ pullback.fst _ _, ?_, ?_, ?_⟩
    · change (t.snd ≫ pullback.fst _ _) ≫ commonNeighborhoodToV R V r = t.fst
      have h := congrArg (fun f => f ≫ pullback.fst _ _) t.condition
      simpa only [Category.assoc, Scheme.Hom.compactificationGraph,
        pullback.lift_fst, Category.comp_id, commonNeighborhoodToGraphAmbient,
        pullback.lift_fst_assoc] using h.symm
    · change (t.snd ≫ pullback.fst _ _) ≫ commonNeighborhoodGraph R V r = t.snd
      apply pullback.hom_ext
      · simp
      · have h := congrArg (fun f => f ≫ pullback.snd _ _) t.condition
        have hf := congrArg (fun f => f ≫ pullback.fst _ _) t.condition
        simp only [Category.assoc, Scheme.Hom.compactificationGraph, pullback.lift_fst,
          Category.comp_id, commonNeighborhoodToGraphAmbient] at hf
        simp only [Category.assoc, Scheme.Hom.compactificationGraph, pullback.lift_snd,
          commonNeighborhoodToGraphAmbient, pullback.lift_snd] at h
        simp only [Category.assoc, commonNeighborhoodGraph_snd, commonNeighborhoodTargetMap_eq]
        simpa only [Category.assoc] using
          (congrArg (fun f => f ≫ neighborhoodInclusion R V) hf.symm).trans h
    · intro m hm hn
      change t.pt ⟶ (commonNeighborhoodSource R V r).toScheme at m
      change m ≫ commonNeighborhoodGraph R V r = t.snd at hn
      change m = t.snd ≫ pullback.fst _ _
      simpa only [Category.assoc, commonNeighborhoodGraph_fst, Category.comp_id] using
        congrArg (fun f => f ≫ pullback.fst _ _) hn)⟩
end AlgebraicGeometry.RelativeProjectiveLine
