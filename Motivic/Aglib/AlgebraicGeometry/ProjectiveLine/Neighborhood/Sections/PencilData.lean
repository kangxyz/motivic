/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Pencil.SpanGeometry
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.SourceFamily
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Sections.Pencils
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Pencils.GraphDivisorData
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
/-! # Actual relative neighborhood sections supply the correcting correspondence data -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
open _root_.AlgebraicGeometry.Scheme.SmoothSite
variable (k R : Type u) [Field k] [CommRing R]
  (bR : Spec (.of R) ⟶ Spec (.of k)) [Smooth bR]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
  (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
  (r : R)

/-- No cycle or family hypothesis: every required finite-flat and regular factor comes from
these original prescribed sections and their actual whole-boundary unit values. -/
def NeighborhoodPencilSections.correspondenceData (P : NeighborhoodPencilSections R V hV r) :
    GraphDivisorPencil.Data (neighborhoodPencilAlpha k R bR V r)
      (neighborhoodPencilBeta k R bR V r) (neighborhoodPencilGraph k R bR V r) := by
  have := neighborhoodLambdaCurve_affine R V r
  have := fixedPsiRetainedCurve_affine R r V
  have := commonNeighborhoodRetainedCurve_affine R V r
  have hAffineA : IsAffineHom (neighborhoodLambdaSourceMap R V r ≫
      (neighborhoodLambdaSite k R bR V r).hom) := by
    have : IsAffine ((Functor.fromPUnit (Spec (.of k))).obj
        (neighborhoodLambdaSite k R bR V r).right) := by
      change IsAffine (Spec (.of k))
      infer_instance
    exact isAffineHom_of_isAffine _
  have hA := neighborhoodLambda_total_smooth k R bR V r
  have hN := neighborhoodPsi_total_smooth k R bR V r
  have hD := neighborhoodCommon_total_smooth k R bR V r
  have ha := P.lambda.normalizedNumerator_finite_flat
  have hb := P.lambda.normalizedDenominator_finite_flat
  have hn := P.psiNumerator_finite_flat
  have hd := P.psiDenominator_finite_flat
  have := P.psiNumerator_unit
  have := P.psiDenominator_unit
  have hp := P.lambda.source_pole_finite_flat R V hV r P.lambdaDegree P.psiDegree P.frame
    P.psiDenominator
  have hf := P.lambda.source_family_finite_flat R V hV r P.lambdaDegree P.psiDegree P.frame
    (neighborhoodCommonSite k R bR V r).hom P.psiNumerator P.psiDenominator P.psi_value
  dsimp only at hp hf
  simp only [commonNeighborhoodRetainedInclusion_fst] at hp
  rw [commonNeighborhoodRetainedInclusion_fst] at hf
  refine {
    C := neighborhoodLambdaCurve R V r
    E := fixedPsiRetainedCurve R r V
    D := commonNeighborhoodRetainedCurve R V r
    qA := neighborhoodLambdaSourceMap R V r
    rA := neighborhoodLambdaTargetMap R V r
    hA := neighborhoodLambda_base k R bR V r
    qN := neighborhoodPsiSourceMap R V r
    rN := neighborhoodPsiTargetMap R V r
    hN := neighborhoodPsi_base k R bR V r
    jA := commonNeighborhoodRetainedToSection R V r
    jN := commonNeighborhoodRetainedToPsi R V r
    p := neighborhoodCommonSourceMap R V r
    squareA := commonNeighborhoodRetainedToSection_source_isPullback R V r
    squareN := commonNeighborhoodRetainedToPsi_isPullback R V r
    g := neighborhoodCommonTargetMap R V r
    targetA := commonNeighborhoodRetainedToSection_target R V r
    targetN := commonNeighborhoodRetainedToPsi_snd R V r
    base := neighborhoodCommon_base k R bR V r
    A := pullbackLineBundle (neighborhoodRetainedInclusion R V ∣_ neighborhoodSectionOpen R V r)
      (dualLineBundle _ (tensorLineBundle _ (neighborhoodLocalTwist R V r P.lambdaDegree)
        (dualLineBundle _ (neighborhoodLocalIdeal R V r))))
    B := pullbackLineBundle (neighborhoodRetainedInclusion R V ∣_ neighborhoodSectionOpen R V r)
      (dualLineBundle _ (neighborhoodLocalTwist R V r P.lambdaDegree))
    N := pullbackLineBundle (fixedPsiRetainedInclusion R r V)
      (dualLineBundle _ (fixedPsiTwistLine R r P.psiDegree))
    M := pullbackLineBundle (fixedPsiRetainedInclusion R r V)
      (dualLineBundle _ (fixedPsiTwistLine R r P.psiDegree))
    a := Scheme.Modules.Hom.pullbackToUnit
      (sectionDualFunctional _ (tensorLineBundle _ (neighborhoodLocalTwist R V r P.lambdaDegree)
        (dualLineBundle _ (neighborhoodLocalIdeal R V r))) P.lambda.normalizedNumerator)
      (neighborhoodRetainedInclusion R V ∣_ neighborhoodSectionOpen R V r)
    b := Scheme.Modules.Hom.pullbackToUnit
      (sectionDualFunctional _ (neighborhoodLocalTwist R V r P.lambdaDegree)
        P.lambda.normalizedDenominator)
      (neighborhoodRetainedInclusion R V ∣_ neighborhoodSectionOpen R V r)
    n := Scheme.Modules.Hom.pullbackToUnit
      (sectionDualFunctional _ (fixedPsiTwistLine R r P.psiDegree) P.psiNumerator)
      (fixedPsiRetainedInclusion R r V)
    d := Scheme.Modules.Hom.pullbackToUnit
      (sectionDualFunctional _ (fixedPsiTwistLine R r P.psiDegree) P.psiDenominator)
      (fixedPsiRetainedInclusion R r V)
    diagonal := commonNeighborhoodRetainedGraph R V r
    diagonal_closed := inferInstance
    diagonal_source := commonNeighborhoodRetainedGraph_fst R V r
    diagonal_target := commonNeighborhoodRetainedGraph_snd R V r
    diagonal_line := (commonNeighborhoodRetainedGraphLine R V r).property
    alpha_flat := by
      change Flat (commonNeighborhoodToSectionSource R V r)
      infer_instance
    beta_flat := by
      change Flat (commonNeighborhoodToPsi R V r)
      infer_instance
    a_regular := ha.2.2.2.2.1
    b_regular := hb.2.2.2.2.1
    n_regular := hn.2.2.2.2.1
    d_regular := hd.2.2.2.2.1
    a_finite := ha.2.2.2.1
    a_flat := ha.2.2.2.2.2
    b_finite := hb.2.2.2.1
    b_flat := hb.2.2.2.2.2
    n_finite := ?_
    n_flat := ?_
    d_finite := ?_
    d_flat := ?_
    qA_smooth := hA
    qA_separated := inferInstance
    qA_quasiCompact := by
      let := hAffineA
      exact quasiCompact_iff_forall_isAffineOpen.mpr fun _ hU =>
        (hU.preimage _).isCompact
    qN_smooth := hN
    qN_separated := inferInstance
    qN_quasiCompact := inferInstance
    p_smooth := hD
    p_separated := inferInstance
    p_quasiCompact := inferInstance
    lineIso := commonNeighborhoodSourcePencilIso R V r P.lambdaDegree P.psiDegree
    pole_finite := hp.1
    pole_flat := hp.2
    family_finite := hf.1
    family_flat := hf.2 }
  all_goals first
    | simpa only [fixedPsiRetainedInclusion_fst] using hn.2.2.2.1
    | simpa only [fixedPsiRetainedInclusion_fst] using hn.2.2.2.2.2
    | simpa only [fixedPsiRetainedInclusion_fst] using hd.2.2.2.1
    | simpa only [fixedPsiRetainedInclusion_fst] using hd.2.2.2.2.2
end AlgebraicGeometry.RelativeProjectiveLine
