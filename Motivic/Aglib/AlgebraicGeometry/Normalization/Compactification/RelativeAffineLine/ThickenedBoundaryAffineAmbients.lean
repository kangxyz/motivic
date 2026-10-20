/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NormalizedBoundaryChoice
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.FixedThickenedBoundaryAffineAmbients

/-! # Affine ambients for the original thickened boundaries before section choice

The finite/free coefficient restriction and thickened boundary are chosen once.
The two later coefficient localizations keep that boundary by literal pullback.
No section datum, frame or replacement normalization is chosen here. This is
an affine-boundary-neighborhood pilot, not a standard-triple splitting theorem.

Intended upstream module:
`ThickenedBoundaryAffineAmbients` in
`Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine`.
Standalone API; no current external import consumer.
The interfaces and exact hypotheses are given in the declarations below.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom RelativeProjectiveLine Scheme.RelativeCurvePencil
universe u



namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] {Y Z : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (z : Z ⟶ Spec (.of (Polynomial R))) [IsClosedImmersion z]
  [IsFinite (z ≫ boundaryLineProjection R)] (s : Z ⟶ Y) (hs : s ≫ p = z)

/-- Retain every original finite/free and thickened-boundary witness, then add
actual affine ambients for the whole source and target boundary pullbacks. -/
def OriginalThickenedBoundaryAffineAmbients : Prop :=
    ∃ (r : R), r ≠ 0 ∧
      (∀ i : ULift.{u} (Fin 2),
        let A := Localization.Away r
        let g := RelativeProjectiveLine.chart A i ≫
          ProjectiveSpace.map (algebraMap R A) (ULift.{u} (Fin 2))
        let : Algebra (Polynomial A) Γ(pullback (toProjectiveLine R p) g, ⊤) :=
          (FiniteSchemeNormBaseChange.scalarMap (pullback.snd (toProjectiveLine R p) g)).toAlgebra
        Module.Free (Polynomial A) Γ(pullback (toProjectiveLine R p) g, ⊤)) ∧
      ∃ (O : (Spec (.of R)).Opens) (hO : IsAffineOpen O),
        let : IsAffine O.toScheme := hO
        genericPoint (Spec (.of R)) ∈ O ∧ O ≤ PrimeSpectrum.basicOpen r ∧
        let F := boundaryBaseProjectiveMap R (ULift (Fin 2)) (toProjectiveLine R p) O
        let J := boundaryBaseCoverInclusion (boundaryLineProjection R) p (projection R p)
          (inclusion R p) (inclusion_projection R p) ⊤ O
        let dOld := boundaryBaseWholeMap (projection R p) (infinityInclusion R p) O
        let sO := boundaryBaseCoverLift (boundaryLineProjection R) p z s hs ⊤ O
          (fun _ _ => trivial)
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
            c ≫ d' = pullback.fst F (neighborhoodBoundaryInclusion Γ(O.toScheme, ⊤) ⊤) ∧
            ProjectiveSpace.SourceTargetFullBoundaryAffineAmbients Γ(O.toScheme, ⊤) F
              (coprod.desc d' (sO ≫ J))
              (coprod.desc (neighborhoodBoundaryInclusion Γ(O.toScheme, ⊤) ⊤)
                (targetNativeMarked R O z ≫ chart Γ(O.toScheme, ⊤) 0))

/-- Construct both actual ambients from the original marked cover, before any
common section choice. Neither source nonemptiness nor positive rank is assumed. -/
theorem exists_originalThickenedBoundaryAffineAmbients
    (H : IsPullback s (𝟙 Z) p z) :
    OriginalThickenedBoundaryAffineAmbients R p z s hs := by
  obtain ⟨r, hr, hfree, O, hO, hηO, hOr, D', d', hdc, hdr, hdj, hds,
    hdf, a, b, c, ha, hb, hc⟩ := exists_common_restricted_thickened_boundary R p z s hs H
  let : IsAffine O.toScheme := hO
  have hamb := fixedThickenedBoundary_fullBoundary_affineAmbients R p z s hs O
    (genericPoint (Spec (.of R))) hηO d' hdc hdf hds H
  exact ⟨r, hr, hfree, O, hO, hηO, hOr, D', d', hdc, hdr, hdj, hds,
    hdf, a, b, c, ha, hb, hc, hamb.2.2.2.2⟩

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
