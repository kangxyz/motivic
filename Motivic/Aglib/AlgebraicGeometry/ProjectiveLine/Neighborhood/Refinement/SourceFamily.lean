/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.SourcePencilIso
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Pencil.OverField
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.Polynomial.PrecompIso
/-! # The actual source-factor polynomial family and constant pole are finite flat -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
  (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
  (r : R) (l m : ℕ) (e : neighborhoodFrame R V r l)

/-- The product of the retained pullbacks of the normalized denominator functional and the
functional of `t`. -/
def NeighborhoodSectionPair.sourcePoleFunctional (d : NeighborhoodSectionPair R V hV r l e)
    (t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val) :=
  Scheme.Modules.Hom.productSection
    (commonNeighborhoodRetainedLambdaFunctional R V r
      (sectionDualFunctional _ (neighborhoodLocalTwist R V r l) d.normalizedDenominator))
    (commonNeighborhoodRetainedPsiFunctional R V r
      (sectionDualFunctional _ (fixedPsiTwistLine R r m) t))

/-- The product of the retained pullbacks of the normalized numerator functional and the
functional of `n`. -/
def NeighborhoodSectionPair.sourceNumeratorFunctional (d : NeighborhoodSectionPair R V hV r l e)
    (n : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val) :=
  Scheme.Modules.Hom.productSection
    (commonNeighborhoodRetainedLambdaFunctional R V r
      (sectionDualFunctional _ (tensorLineBundle _ (neighborhoodLocalTwist R V r l)
        (dualLineBundle _ (neighborhoodLocalIdeal R V r))) d.normalizedNumerator))
    (commonNeighborhoodRetainedPsiFunctional R V r
      (sectionDualFunctional _ (fixedPsiTwistLine R r m) n))

lemma NeighborhoodSectionPair.source_pole_finite_flat
    (d : NeighborhoodSectionPair R V hV r l e)
    (t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val)
    [IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) t)] :
    let p := commonNeighborhoodRetainedInclusion R V r ≫
      pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _)
    IsFinite (Scheme.Modules.Hom.zeroInclusion (d.sourcePoleFunctional R V hV r l m e t) ≫ p) ∧
      Flat (Scheme.Modules.Hom.zeroInclusion (d.sourcePoleFunctional R V hV r l m e t) ≫ p) := by
  let p := commonNeighborhoodRetainedInclusion R V r ≫
    pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _)
  let a := Scheme.Modules.Hom.pullbackToUnit (d.poleFunctional R V hV r l m e t)
    (commonNeighborhoodRetainedInclusion R V r)
  let E := commonNeighborhoodRetainedProductPullbackIso R V r
    (dualLineBundle _ (neighborhoodLocalTwist R V r l))
    (dualLineBundle _ (fixedPsiTwistLine R r m))
  have he : E.hom ≫ a = d.sourcePoleFunctional R V hV r l m e t :=
    commonNeighborhoodRetainedProductPullbackIso_functional R V r _ _ _ _
  obtain ⟨hf, _, hg⟩ := d.pole_finite_mono_flat R V hV r l m e t
  let : IsFinite (Scheme.Modules.Hom.zeroInclusion a ≫ p) := hf
  let : Flat (Scheme.Modules.Hom.zeroInclusion a ≫ p) := hg
  have hfin : IsFinite (Scheme.Modules.Hom.zeroInclusion (E.hom ≫ a) ≫ p) := by
    rw [← zeroSchemePrecompIso_hom_inclusion E a, Category.assoc]
    infer_instance
  have hflat : Flat (Scheme.Modules.Hom.zeroInclusion (E.hom ≫ a) ≫ p) := by
    rw [← zeroSchemePrecompIso_hom_inclusion E a, Category.assoc]
    infer_instance
  rw [he] at hfin hflat
  exact ⟨hfin, hflat⟩

theorem NeighborhoodSectionPair.source_family_finite_flat
    {K : Type u} [Field K] (bS : (commonNeighborhoodSource R V r).toScheme ⟶ Spec (.of K))
    (d : NeighborhoodSectionPair R V hV r l e)
    (n t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val)
    [IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) n)]
    (hn : pullbackSectionMap (fixedPsiBoundaryMap R r V) n =
      (fixedPsiBoundaryUnit R V r).hom ≫ pullbackSectionMap (fixedPsiBoundaryMap R r V) t) :
    let p := commonNeighborhoodRetainedInclusion R V r ≫
      pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _)
    let f := familyMap (p ≫ bS) (commonNeighborhoodSourceGraphLine R V r l m)
      (Scheme.Modules.Hom.productSection
        (Scheme.Hom.idealInclusion (commonNeighborhoodRetainedGraph R V r))
        (d.sourcePoleFunctional R V hV r l m e t))
      ((commonNeighborhoodSourcePencilIso R V r l m).hom ≫
        d.sourceNumeratorFunctional R V hV r l m e n)
    IsFinite (Scheme.Modules.Hom.zeroInclusion f ≫ parameterMap bS p) ∧
      Flat (Scheme.Modules.Hom.zeroInclusion f ≫ parameterMap bS p) := by
  let j := commonNeighborhoodRetainedInclusion R V r
  let p := j ≫ pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _)
  let L := commonNeighborhoodSourceGraphLine R V r l m
  let M := pullbackLineBundle j (commonNeighborhoodPencilLine R V r l m)
  let E := commonNeighborhoodSourceCompactIso R V r l m
  let a := Scheme.Modules.Hom.pullbackToUnit (d.pencilStart R V hV r l m e t) j
  let c := Scheme.Modules.Hom.pullbackToUnit (d.pencilEnd R V hV r l m e n) j
  obtain ⟨hfin, hflat⟩ := d.common_family_finite_flat_over R V hV r l m e bS n t hn
  let : IsFinite (Scheme.Modules.Hom.zeroInclusion (familyMap (p ≫ bS) M a c) ≫
      parameterMap bS p) := hfin
  let : Flat (Scheme.Modules.Hom.zeroInclusion (familyMap (p ≫ bS) M a c) ≫
      parameterMap bS p) := hflat
  have hf := familyZeroPrecomp_isFinite (p ≫ bS) L M E a c (parameterMap bS p)
  have hg := familyZeroPrecomp_flat (p ≫ bS) L M E a c (parameterMap bS p)
  dsimp only [E, a, c] at hf hg
  rw [d.sourceCompactIso_start R V r l m hV e t,
    d.sourceCompactIso_end R V r l m hV e n] at hf hg
  exact ⟨hf, hg⟩
end AlgebraicGeometry.RelativeProjectiveLine
