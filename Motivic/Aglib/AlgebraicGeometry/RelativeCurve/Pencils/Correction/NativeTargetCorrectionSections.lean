/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.NativeSimultaneousSectionChoice
/-! # Transport the same target section record across the identity structure map

The target producer uses `id ≫ toSpec`. The norm consumer uses `toSpec`.
We transport the whole dependent existential record by this map equality;
there is no second Serre choice and no independently chosen boundary frame.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.NativeTargetCorrectionSections`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumer:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalTargetSectionWitnesses`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom RelativeProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

local instance (B : Type u) [CommRing B] :
    SmoothOfRelativeDimension 1 (boundaryLineProjection B) :=
  Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one B

local instance (B : Type u) [CommRing B] :
    SmoothOfRelativeDimension 1
      (chart B 0 ≫ toSpec B (ULift.{u} (Fin 2))) := by
  rw [chart_toSpec]
  infer_instance

local instance (B : Type u) [CommRing B] :
    SmoothOfRelativeDimension 1
      (chart B 0 ≫ ((𝟙 _) ≫ toSpec B (ULift.{u} (Fin 2)))) := by
  simpa only [Category.id_comp] using
    (inferInstance : SmoothOfRelativeDimension 1
      (chart B 0 ≫ toSpec B (ULift.{u} (Fin 2))))

variable (R : Type u) [CommRing R]
  (V : (Spec (.of R)).Opens) [IsAffine V.toScheme]
  {Z D T : Scheme.{u}} (z : Z ⟶ Spec (.of (Polynomial R)))
  [IsFinite (z ≫ boundaryLineProjection R)]
  (d : D ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
  (hd : Disjoint (Set.range (chart R 0)) (Set.range d))
  (v : T ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))

/-- Equality transport of the complete original target pair, including its
same full-boundary frame, both units and both original divisor records. -/
theorem exists_nativeTargetCorrectionSections
    (h : NativeTargetBoundarySections (R := R) (z := z) (V := V)
      (d₀ := d) (hd₀ := hd) (v₀ := v)) :
    let π := toSpec Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2))
    let j := chart Γ(V.toScheme, ⊤) 0
    let zN := targetNativeMarked R V z
    let dN := targetNativeInfinity R V d
    let b := coprod.desc (infinityProductMap π j dN) (graphBoundaryRestriction π j zN)
    let i := retainedProductInclusion (j ≫ π) π (targetNativeRetained R V v)
    ∃ L : LineBundle (pullback (j ≫ π) π),
    ∃ aS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
      (tensorLineBundle _ L (dualLineBundle _ (relativeCompactificationGraphLine π j))).val,
    ∃ bS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ L.val,
      pullbackSectionMap b aS ≫ pullbackTensorMap b L.val
        (dualLineBundle _ (relativeCompactificationGraphLine π j)).val =
      tensorUnitSection (pullbackSectionMap b bS)
        (relativeFullBoundaryFrame (boundaryLineProjection Γ(V.toScheme, ⊤)) π j
          (𝟙 _) ((chart_toSpec Γ(V.toScheme, ⊤) 0).trans
            (Category.id_comp (boundaryLineProjection Γ(V.toScheme, ⊤))).symm)
          zN zN (Category.comp_id zN) (IsPullback.id_vert zN)
          (targetNativeCanonicalFrame R V z) dN (targetNativeInfinity_disjoint R V d hd)).inv ∧
      IsIso (pullbackSectionMap b aS) ∧ IsIso (pullbackSectionMap b bS) ∧
      CoherentGraph.SectionDivisorFiniteFlat (pullback.fst (j ≫ π) π) i
        (tensorLineBundle _ L (dualLineBundle _ (relativeCompactificationGraphLine π j))) aS ∧
      CoherentGraph.SectionDivisorFiniteFlat (pullback.fst (j ≫ π) π) i L bS := by
  let B := Γ(V.toScheme, ⊤)
  let π₀ := toSpec B (ULift.{u} (Fin 2))
  let j := chart B 0
  let zN := targetNativeMarked R V z
  let dN := targetNativeInfinity R V d
  let P := fun (π : ProjectiveSpace B (ULift.{u} (Fin 2)) ⟶ Spec (.of B))
      (hsep : IsSeparated π) (hsm : SmoothOfRelativeDimension 1 (j ≫ π))
      (hq : j ≫ π = (𝟙 _) ≫ boundaryLineProjection B) =>
    letI := hsep
    letI := hsm
    let b := fullBoundaryProductMap π j dN zN
    let i := retainedProductInclusion (j ≫ π) π (targetNativeRetained R V v)
    ∃ L : LineBundle (pullback (j ≫ π) π),
      ∃ aS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
        (tensorLineBundle _ L
          (dualLineBundle _ (relativeCompactificationGraphLine π j))).val,
      ∃ bS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ L.val,
        pullbackSectionMap b aS ≫ pullbackTensorMap b L.val
          (dualLineBundle _ (relativeCompactificationGraphLine π j)).val =
        tensorUnitSection (pullbackSectionMap b bS)
          (relativeFullBoundaryFrame (boundaryLineProjection B) π j (𝟙 _) hq
            zN zN (Category.comp_id zN) (IsPullback.id_vert zN)
            (targetNativeCanonicalFrame R V z) dN
            (targetNativeInfinity_disjoint R V d hd)).inv ∧
        IsIso (pullbackSectionMap b aS) ∧ IsIso (pullbackSectionMap b bS) ∧
        CoherentGraph.SectionDivisorFiniteFlat (pullback.fst (j ≫ π) π) i
          (tensorLineBundle _ L
            (dualLineBundle _ (relativeCompactificationGraphLine π j))) aS ∧
        CoherentGraph.SectionDivisorFiniteFlat (pullback.fst (j ≫ π) π) i L bS
  have hq₀ : j ≫ π₀ = (𝟙 _) ≫ boundaryLineProjection B :=
    (chart_toSpec B 0).trans (Category.id_comp _).symm
  have hq₁ : j ≫ ((𝟙 _) ≫ π₀) = (𝟙 _) ≫ boundaryLineProjection B :=
    (congrArg (fun t => j ≫ t) (Category.id_comp π₀)).trans hq₀
  have hwhole : P ((𝟙 _) ≫ π₀) inferInstance inferInstance hq₁ := by
    dsimp only [NativeTargetBoundarySections, targetFullBoundaryFrame] at h
    obtain ⟨degree, pair⟩ := h
    let L := pullbackLineBundle
      (ConstantCurve.affineSourceToProjectiveSpace B (ULift.{u} (Fin 2))
        (j ≫ ((𝟙 _) ≫ π₀)) (𝟙 _))
      (twistingLineBundle Γ(Spec (.of (Polynomial B)), ⊤)
        (ULift.{u} (Fin 2)) (degree : ℤ))
    with_reducible exact ⟨L, pair⟩
  have transport : ∀ π (heq : π = π₀) hsep hsm hq,
      P π hsep hsm hq → P π₀ inferInstance inferInstance hq₀ := by
    intro π heq
    subst π
    intro hsep hsm hq hp
    with_reducible exact hp
  have hout := transport _ (Category.id_comp π₀) _ _ _ hwhole
  dsimp only [P, fullBoundaryProductMap] at hout
  with_reducible exact hout

end AlgebraicGeometry.Scheme.RelativeCurvePencil
