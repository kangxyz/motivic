/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Retained.PencilIso
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Pencil.OverField
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.Polynomial.PrecompIso
/-! # The whole finite-flat family in the original graph-times-pole coefficient -/
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

theorem NeighborhoodSectionPair.graph_family_finite_flat
    {K : Type u} [Field K] (bS : (commonNeighborhoodSource R V r).toScheme ⟶ Spec (.of K))
    (d : NeighborhoodSectionPair R V hV r l e)
    (n t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val)
    [IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) n)]
    (hn : pullbackSectionMap (fixedPsiBoundaryMap R r V) n =
      (fixedPsiBoundaryUnit R V r).hom ≫ pullbackSectionMap (fixedPsiBoundaryMap R r V) t) :
    let j := commonNeighborhoodRetainedInclusion R V r
    let p := j ≫ pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _)
    let a := Scheme.Modules.Hom.productSection
      (Scheme.Hom.idealInclusion (commonNeighborhoodRetainedGraph R V r))
      (Scheme.Modules.Hom.pullbackToUnit (d.poleFunctional R V hV r l m e t) j)
    let c := (commonNeighborhoodRetainedPencilIso R V r l m).hom ≫
      Scheme.Modules.Hom.pullbackToUnit (d.pencilEnd R V hV r l m e n) j
    let f := familyMap (p ≫ bS) (commonNeighborhoodGraphDomainLine R V r l m) a c
    IsFinite (Scheme.Modules.Hom.zeroInclusion f ≫ parameterMap bS p) ∧
      Flat (Scheme.Modules.Hom.zeroInclusion f ≫ parameterMap bS p) := by
  let j := commonNeighborhoodRetainedInclusion R V r
  let p := j ≫ pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _)
  let L := commonNeighborhoodGraphDomainLine R V r l m
  let M := pullbackLineBundle j (commonNeighborhoodPencilLine R V r l m)
  let E := commonNeighborhoodRetainedPencilIso R V r l m
  let a := Scheme.Modules.Hom.pullbackToUnit (d.pencilStart R V hV r l m e t) j
  let c := Scheme.Modules.Hom.pullbackToUnit (d.pencilEnd R V hV r l m e n) j
  obtain ⟨hfin, hflat⟩ := d.common_family_finite_flat_over R V hV r l m e bS n t hn
  let : IsFinite (Scheme.Modules.Hom.zeroInclusion (familyMap (p ≫ bS) M a c) ≫
      parameterMap bS p) := hfin
  let : Flat (Scheme.Modules.Hom.zeroInclusion (familyMap (p ≫ bS) M a c) ≫
      parameterMap bS p) := hflat
  have hf := familyZeroPrecomp_isFinite (p ≫ bS) L M E a c (parameterMap bS p)
  have hg := familyZeroPrecomp_flat (p ≫ bS) L M E a c (parameterMap bS p)
  dsimp only [E, a] at hf hg
  rw [d.retainedPencilIso_start R V r l m hV e t] at hf hg
  exact ⟨hf, hg⟩
end AlgebraicGeometry.RelativeProjectiveLine
