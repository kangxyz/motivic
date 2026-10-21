/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.NativeTargetCorrectionSections
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeRetainedProduct
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeCanonicalFrame

/-! # Original target-section witnesses

The eight original target-section witnesses are held in one geometric record.
The producer packages the actual native correction-section supplier without
replacing its choices, boundary frame or retained divisor map. Current consumers
are the native middle input and its two-localization history.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalTargetSectionWitnesses`.

The exact hypotheses are the record fields and declaration signatures below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme Scheme.Hom Scheme.Modules Scheme.Modules.Invertible RelativeProjectiveLine
open Scheme.RelativeCurvePencil
universe u

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

attribute [local instance]
  Scheme.RelativeCurvePencil.nativeTargetCorrectionSectionsSmoothRelativeDimension1
  Scheme.RelativeCurvePencil.nativeTargetCorrectionSectionsSmoothRelativeDimension2

variable (R : Type u) [CommRing R] {Z D WA : Scheme.{u}}
  (z : Z ⟶ Spec (.of (Polynomial R)))
  (e : SheafOfModules.unit (pullback (boundaryLineProjection R)
    (z ≫ boundaryLineProjection R)).ringCatSheaf ≅
      idealModule (boundaryGraphTarget (boundaryLineProjection R) z))
  (dA : D ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
  (hdA : Disjoint (Set.range (chart R 0)) (Set.range dA))
  (iA : WA ⟶ pullback
    (chart R 0 ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) [IsOpenImmersion iA]

/-- The actual original eight-field target choice, first typed on free geometry.
The full boundary frame and original retained divisor map are unchanged. -/
structure OriginalTargetSectionWitnesses where
  /-- The original LA input. -/
  LA : LineBundle (pullback ((chart R 0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))
  /-- The original aA input. -/
  aA : SheafOfModules.unit (pullback ((chart R 0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin
    2)))) (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))).ringCatSheaf ⟶
    (tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R 0)))).val
  /-- The original bA input. -/
  bA : SheafOfModules.unit (pullback ((chart R 0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin
    2)))) (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))).ringCatSheaf ⟶ LA.val
  /-- The original hFa input. -/
  hFa : CoherentGraph.SectionDivisorFiniteFlat (pullback.fst ((chart R 0) ≫
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) (ProjectiveSpace.toSpec R (ULift.{u} (Fin
    2)))) iA
    (tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R 0)))) aA
  /-- The original hFb input. -/
  hFb : CoherentGraph.SectionDivisorFiniteFlat (pullback.fst ((chart R 0) ≫
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) (ProjectiveSpace.toSpec R (ULift.{u} (Fin
    2)))) iA LA bA
  /-- The original hpairA input. -/
  hpairA :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let j := chart R 0
    let b := coprod.desc (infinityProductMap π j dA) (graphBoundaryRestriction π j z)
    pullbackSectionMap b aA ≫
      pullbackTensorMap b LA.val
        (dualLineBundle _ (relativeCompactificationGraphLine π j)).val =
    tensorUnitSection (pullbackSectionMap b bA)
      (relativeFullBoundaryFrame (boundaryLineProjection R) π j
        (𝟙 _) ((chart_toSpec R 0).trans
          (Category.id_comp (boundaryLineProjection R)).symm)
        z z (Category.comp_id z) (IsPullback.id_vert z) e dA hdA).inv
  /-- The original unitA input. -/
  [unitA : IsIso (pullbackSectionMap (fullBoundaryProductMap (ProjectiveSpace.toSpec R
    (ULift.{u} (Fin 2))) (chart R 0) dA z) aA)]
  /-- The original unitB input. -/
  [unitB : IsIso (pullbackSectionMap (fullBoundaryProductMap (ProjectiveSpace.toSpec R
    (ULift.{u} (Fin 2))) (chart R 0) dA z) bA)]

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

attribute [local instance]
  Scheme.RelativeCurvePencil.nativeTargetCorrectionSectionsSmoothRelativeDimension1
  Scheme.RelativeCurvePencil.nativeTargetCorrectionSectionsSmoothRelativeDimension2


/-- Package the same original target supplier once, without rebuilding its eight types
in a later concrete history. The retained inclusion is the original one. -/
theorem nonempty_originalTargetSectionWitnesses
    (R : Type u) [CommRing R] (V : (Spec (.of R)).Opens) [IsAffine V.toScheme]
    {Z D A : Scheme.{u}} (z : Z ⟶ Spec (.of (Polynomial R)))
    [IsFinite (z ≫ boundaryLineProjection R)]
    (d : D ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
    (hd : Disjoint (Set.range (chart R 0)) (Set.range d))
    (v : A ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
    (h : NativeTargetBoundarySections (R := R) (z := z) (V := V)
      (d₀ := d) (hd₀ := hd) (v₀ := v)) :
    Nonempty (OriginalTargetSectionWitnesses Γ(V.toScheme, ⊤)
      (targetNativeMarked R V z) (targetNativeCanonicalFrame R V z)
      (targetNativeInfinity R V d) (targetNativeInfinity_disjoint R V d hd)
      (retainedProductInclusion
        (chart Γ(V.toScheme, ⊤) 0 ≫
          ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2)))
        (ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2)))
        (targetNativeRetained R V v))) := by
  have chosen := (exists_nativeTargetCorrectionSections R V z d hd v h)
  obtain ⟨LA, aA, bA, hpairA, haA, hbA, hFa, hFb⟩ := chosen
  exact ⟨({
    LA := (LA)
    aA := (aA)
    bA := (bA)
    hFa := (hFa)
    hFb := (hFb)
    hpairA := (hpairA)
    unitA := (haA)
    unitB := (hbA) })⟩


end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
