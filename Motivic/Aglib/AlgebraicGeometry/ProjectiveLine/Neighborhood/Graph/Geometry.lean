/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.ZeroNeighborhoodBoundary
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.EtaleCurve
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.FullBoundaryTrivialization
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.FullBoundaryProduct
/-! # Actual relative neighborhood graph and its prescribed whole boundary -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens)
/-- Include the affine neighborhood into the zero-coordinate chart of the projective line. -/
abbrev neighborhoodInclusion := V.ι ≫ chart R ⟨0⟩
/-- The structural map of the affine neighborhood to `Spec R`. -/
abbrev neighborhoodProjection := neighborhoodInclusion R V ≫
  ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
/-- The projective line pulled back along the neighborhood projection. -/
abbrev neighborhoodGraphAmbient := pullback (neighborhoodProjection R V)
  (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
/-- The affine line pulled back along the neighborhood projection. -/
abbrev neighborhoodAffineAmbient := pullback (neighborhoodProjection R V)
  (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))

/-- The affine-chart map into the graph ambient projective line. -/
def neighborhoodAffineInclusion :
    neighborhoodAffineAmbient R V ⟶ neighborhoodGraphAmbient R V :=
  (IsPullback.of_hasPullback (neighborhoodProjection R V)
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))).flip.lift
      (pullback.snd _ _ ≫ chart R ⟨0⟩) (pullback.fst _ _) (by
        rw [Category.assoc, chart_toSpec, pullback.condition])

@[reassoc (attr := simp)]
lemma neighborhoodAffineInclusion_fst :
    neighborhoodAffineInclusion R V ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (IsPullback.of_hasPullback _ _).flip.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma neighborhoodAffineInclusion_snd :
    neighborhoodAffineInclusion R V ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ chart R ⟨0⟩ :=
  (IsPullback.of_hasPullback _ _).flip.lift_fst _ _ _

lemma neighborhoodAffineInclusion_isPullback :
    IsPullback (pullback.snd _ _) (neighborhoodAffineInclusion R V) (chart R ⟨0⟩)
      (pullback.snd (neighborhoodProjection R V)
        (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) := by
  have H : IsPullback (pullback.snd (neighborhoodProjection R V)
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))))
      (pullback.fst _ _) (chart R ⟨0⟩ ≫ ProjectiveSpace.toSpec R _)
      (neighborhoodProjection R V) := by
    rw [chart_toSpec]
    exact (IsPullback.of_hasPullback _ _).flip
  exact H.of_bot' (IsPullback.of_hasPullback _ _).flip

instance : IsOpenImmersion (neighborhoodAffineInclusion R V) :=
  MorphismProperty.of_isPullback (neighborhoodAffineInclusion_isPullback R V) inferInstance

lemma neighborhoodAffine_smooth : SmoothOfRelativeDimension 1
    (pullback.fst (neighborhoodProjection R V)
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))) := by
  have := Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R
  exact MorphismProperty.pullback_fst _ _ inferInstance

lemma neighborhoodGraph_mem_affine :
    Set.range (Scheme.Hom.compactificationGraph (ProjectiveSpace.toSpec R _)
      (neighborhoodInclusion R V)) ⊆ Set.range (neighborhoodAffineInclusion R V) := by
  let l : V.toScheme ⟶ neighborhoodAffineAmbient R V := pullback.lift (𝟙 _) V.ι (by
    simp only [Category.id_comp, neighborhoodProjection, neighborhoodInclusion,
      Category.assoc, chart_toSpec])
  have hl : l ≫ neighborhoodAffineInclusion R V =
      Scheme.Hom.compactificationGraph (ProjectiveSpace.toSpec R _)
        (neighborhoodInclusion R V) := by
    apply pullback.hom_ext <;>
      simp [l, Scheme.Hom.compactificationGraph, neighborhoodInclusion]
  rintro x ⟨y, rfl⟩
  exact ⟨l y, congrArg (fun f => f y) hl⟩

lemma neighborhoodGraph_affineOpen_smooth : SmoothOfRelativeDimension 1
    ((neighborhoodAffineInclusion R V).opensRange.ι ≫
      pullback.fst (neighborhoodProjection R V) (ProjectiveSpace.toSpec R _)) := by
  rw [← (neighborhoodAffineInclusion R V).isoOpensRange_inv_comp, Category.assoc,
    neighborhoodAffineInclusion_fst]
  have := neighborhoodAffine_smooth R V
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

/-- Actual relative graph ideal, with the smooth neighborhood constructed. -/
lemma neighborhoodGraph_ideal_rankOne : IsLocallyRankOne (neighborhoodGraphAmbient R V)
    (Scheme.Hom.idealModule (Scheme.Hom.compactificationGraph (ProjectiveSpace.toSpec R _)
      (neighborhoodInclusion R V))) := by
  have := neighborhoodGraph_affineOpen_smooth R V
  exact Scheme.Hom.graph_idealModule_isLocallyRankOne (neighborhoodInclusion R V)
    (ProjectiveSpace.toSpec R _) (neighborhoodAffineInclusion R V).opensRange
      (neighborhoodGraph_mem_affine R V)
end AlgebraicGeometry.RelativeProjectiveLine
