/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.CommonCoefficientOpen
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.RestrictedThickenedBoundary

/-! # A single actual normalized thickened boundary before ambient restrictions

The normalization is the canonical one of the given native original cover.
The common generic coefficient open is chosen once, followed by one thickened
boundary. All residual and full inverse-infinity factor maps remain in the output.


Intended upstream module:
Module prefix: `Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.`
Module suffix: `NormalizedBoundaryChoice`.
Incoming project consumers: `Motivic.Transfers.Presheaf.Actions.Norm.RefinedNormalization`.
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

/-- Exact geometric output of the single generic restriction and thickening. -/
def CommonRestrictedThickenedBoundary : Prop :=
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
            c ≫ d' = pullback.fst F (neighborhoodBoundaryInclusion Γ(O.toScheme, ⊤) ⊤)

/-- The generic free/finite-infinity restriction and full thickening are actual
successive constructions, not inputs and not independent normalizations. -/
theorem exists_common_restricted_thickened_boundary
    (H : IsPullback s (𝟙 Z) p z) : CommonRestrictedThickenedBoundary R p z s hs := by
  obtain ⟨r, hr, hfree, O, hO, hηO, hOr, hfinite⟩ := exists_common_coefficient_open R p
  let : IsAffine O.toScheme := hO
  let := hfinite
  refine ⟨r, hr, hfree, O, hO, hηO, hOr, ?_⟩
  exact exists_restricted_thickened_boundary R p O z s hs H

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
