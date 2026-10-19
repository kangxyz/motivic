/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.RestrictedMarkedSquare
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.ThickenedBoundary
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeGeometry
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.ZeroNeighborhoodBoundary

/-! # Construct the thickened boundary of the same restricted normalization

Intended upstream module:
Module prefix: `Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.`
Module suffix: `RestrictedThickenedBoundary`.
Incoming project consumers:
Module prefix: `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.`
Module suffix: `RelativeAffineLine.NormalizedBoundaryChoice`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom RelativeProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] {Y Z : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
  (z : Z ⟶ Spec (.of (Polynomial R))) [IsClosedImmersion z]
  [IsFinite (z ≫ boundaryLineProjection R)] (s : Z ⟶ Y) (hs : s ≫ p = z)

local notation "F" => boundaryBaseProjectiveMap R (ULift (Fin 2)) (toProjectiveLine R p) O
local notation "J" => boundaryBaseCoverInclusion (boundaryLineProjection R) p (projection R p)
  (inclusion R p) (inclusion_projection R p) ⊤ O
local notation "dOld" => boundaryBaseWholeMap (projection R p) (infinityInclusion R p) O
local notation "sO" => boundaryBaseCoverLift (boundaryLineProjection R) p z s hs ⊤ O
  (fun _ _ => trivial)

omit [IsSeparated p] [IsClosedImmersion z] [IsFinite (z ≫ boundaryLineProjection R)] in
/-- The marked triangle on the actual restricted normalization. -/
theorem restricted_marked_toProjectiveLine :
    (sO ≫ J) ≫ F = targetNativeMarked R O z ≫ chart Γ(O.toScheme, ⊤) 0 := by
  rw [Category.assoc, restricted_inclusion_toProjectiveLine, ← Category.assoc,
    sourceNativeCoverLift_map]

/-- Apply the full scheme-theoretic thickening once to the actual coefficient
restriction. The finite old boundary is the output of the initial coefficient-open
constructor, not a claim about the original unshrunk infinity. Target infinity is
the canonical complement of the whole native affine chart. -/
theorem exists_restricted_thickened_boundary
    (H : IsPullback s (𝟙 Z) p z)
    [IsFinite (dOld ≫ pullback.fst O.ι (projection R p))] :
    ∃ (D' : Scheme.{u}) (d' : D' ⟶ boundaryBaseCompactification (projection R p) O),
      IsClosedImmersion d' ∧ Set.range d' = (Set.range J)ᶜ ∧
      Disjoint (Set.range J) (Set.range d') ∧
      Disjoint (Set.range (sO ≫ J)) (Set.range d') ∧
      IsFinite (d' ≫ (F ≫ ProjectiveSpace.toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)))) ∧
      ∃ (a : (((infinityInclusion R p ≫ projection R p) ⁻¹ᵁ O).toScheme) ⟶ D')
        (b : (residualMarkedFiberOpen F J
          (targetNativeMarked R O z ≫ chart Γ(O.toScheme, ⊤) 0) sO
          (restricted_marked_toProjectiveLine R p O z s hs)).toScheme ⟶ D')
        (c : pullback F (neighborhoodBoundaryInclusion Γ(O.toScheme, ⊤) ⊤) ⟶ D'),
        a ≫ d' = dOld ∧ b ≫ d' = residualMarkedFiberMap F J
          (targetNativeMarked R O z ≫ chart Γ(O.toScheme, ⊤) 0) sO
          (restricted_marked_toProjectiveLine R p O z s hs) ∧
        c ≫ d' = pullback.fst F (neighborhoodBoundaryInclusion Γ(O.toScheme, ⊤) ⊤) := by
  have : IsOpenImmersion J := boundaryBaseCoverInclusion_open ..
  have : IsProper ((z ≫ chart R 0) ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
    rw [Category.assoc, chart_toSpec]
    infer_instance
  have : IsProper (z ≫ chart R 0) := by
    apply IsProper.of_comp _ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
  have : IsClosedImmersion (z ≫ chart R 0) :=
    IsClosedImmersion.of_isPreimmersion _ (z ≫ chart R 0).isClosedMap.isClosed_range
  have : IsFinite (dOld ≫
      (F ≫ ProjectiveSpace.toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)))) := by
    rw [boundaryBaseProjectiveMap_toSpec]
    simpa only [Category.assoc] using
      (inferInstance : IsFinite ((dOld ≫ pullback.fst O.ι (projection R p)) ≫
        O.toScheme.isoSpec.hom))
  have hd : Set.range dOld = (Set.range J)ᶜ := by
    ext x
    change x ∈ Set.range dOld ↔ ¬ x ∈ Set.range J
    rw [mem_range_boundaryBaseWholeMap_iff, mem_range_restricted_inclusion_iff]
    rw [EtaleCompactification.range_infinityInclusion]
    rfl
  have hi : Disjoint (Set.range (chart Γ(O.toScheme, ⊤) 0))
      (Set.range (neighborhoodBoundaryInclusion Γ(O.toScheme, ⊤) ⊤)) := by
    rw [range_neighborhoodBoundaryInclusion]
    apply Set.disjoint_left.mpr
    rintro x ⟨y, rfl⟩ hx
    exact hx ⟨y, trivial, rfl⟩
  exact exists_thickened_compactification_boundary F
    (F ≫ ProjectiveSpace.toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2))) J dOld hd
    (targetNativeMarked R O z ≫ chart Γ(O.toScheme, ⊤) 0) sO
    (restricted_marked_toProjectiveLine R p O z s hs)
    (restricted_marked_projective_isPullback R p O z s hs H)
    (neighborhoodBoundaryInclusion Γ(O.toScheme, ⊤) ⊤)
    (sourceNativeCoverMap R O p) (chart Γ(O.toScheme, ⊤) 0)
    (restricted_inclusion_toProjectiveLine R p O).symm hi

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
