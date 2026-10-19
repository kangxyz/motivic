/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NormalizedBoundaryChoice
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NativeComplement
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.OriginalOverlapSectionChoice
/-! # One normalization and its original simultaneous sections

The normalization is the canonical one of the given native original cover.
The common generic coefficient open is chosen once, followed by one thickened
boundary. All residual and full inverse-infinity factor maps remain in the output.

Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.OriginalSectionChoice`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Norm.RefinedSectionChoice`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom RelativeProjectiveLine Scheme.RelativeCurvePencil
universe u
namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
local instance {S X Y C : Scheme.{u}} (q : X ⟶ S) (p : Y ⟶ X)
    (π : C ⟶ S) (j : Y ⟶ C) [IsOpenImmersion j] (hj : j ≫ π = p ≫ q)
    (U : X.Opens) (V : S.Opens) :
    IsOpenImmersion (boundaryBaseCoverInclusion q p π j hj U V) :=
  boundaryBaseCoverInclusion_open q p π j hj U V

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] {Y A Z : Scheme.{u}} [IsAffine Y] [IsAffine A]
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (z : Z ⟶ Spec (.of (Polynomial R))) [IsClosedImmersion z]
  [IsFinite (z ≫ boundaryLineProjection R)] (s : Z ⟶ Y) (hs : s ≫ p = z)


variable (a₀ : A ⟶ Spec (.of (Polynomial R))) [IsOpenImmersion a₀]
  (H : IsPullback s (𝟙 Z) p z)

/-- One normalization, its exact factors and free charts, and one section choice. -/
def NormalizedOriginalSectionChoice : Prop :=
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
            ∃ x : Spec Γ(O.toScheme, ⊤),
            OriginalOverlapCommonSections Γ(O.toScheme, ⊤)
              (sourceNativeCoverMap R O p) (sourceNativeCoverMap R O a₀)
              (targetNativeMarked R O z) sO
              (sourceNativeCoverLift_isPullback R O z p s hs H) J d' F
              ⊤ x

/-- Construct the sections only after the one fixed normalization restriction and
thickening, preserving both complete free charts and every full boundary factor. -/
theorem exists_normalizedOriginalSectionChoice
    (hz : Set.range z = (Set.range a₀)ᶜ) :
    NormalizedOriginalSectionChoice R p z s hs a₀ H := by
  obtain ⟨r, hr, hfree, O, hO, hηO, hOr, D', d', hdc, hdr, hdj, hds,
    hdf, a, b, c, ha, hb, hc⟩ := exists_common_restricted_thickened_boundary R p z s hs H
  let : IsAffine O.toScheme := hO
  let : IsNoetherianRing Γ(O.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have : IsClosedImmersion s := MorphismProperty.of_isPullback H.flip inferInstance
  have : IsProper ((s ≫ inclusion R p) ≫ projection R p) := by
    rw [Category.assoc, inclusion_projection, ← Category.assoc, hs]
    infer_instance
  have : IsProper (s ≫ inclusion R p) := IsProper.of_comp _ (projection R p)
  have : IsClosedImmersion (s ≫ inclusion R p) :=
    IsClosedImmersion.of_isPreimmersion _ (s ≫ inclusion R p).isClosedMap.isClosed_range
  let F := boundaryBaseProjectiveMap R (ULift (Fin 2)) (toProjectiveLine R p) O
  let J := boundaryBaseCoverInclusion (boundaryLineProjection R) p (projection R p)
    (inclusion R p) (inclusion_projection R p) ⊤ O
  let sO := boundaryBaseCoverLift (boundaryLineProjection R) p z s hs ⊤ O
    (fun _ _ => trivial)
  let : IsClosedImmersion d' := hdc
  let : IsFinite (d' ≫ (F ≫ ProjectiveSpace.toSpec Γ(O.toScheme, ⊤)
    (ULift.{u} (Fin 2)))) := hdf
  have : IsOpenImmersion J := boundaryBaseCoverInclusion_open ..
  have : IsClosedImmersion (sO ≫ J) :=
    boundaryBaseSourceZero_closed (boundaryLineProjection R) p z s hs
      (projection R p) (inclusion R p) (inclusion_projection R p) ⊤ O
      (fun _ _ => trivial)
  refine ⟨r, hr, hfree, O, hO, hηO, hOr, D', d', hdc, hdr, hdj, hds,
    hdf, a, b, c, ha, hb, hc,
    O.toScheme.isoSpec.hom ⟨genericPoint (Spec (.of R)), hηO⟩, ?_⟩
  exact exists_originalOverlap_common_boundary_sections Γ(O.toScheme, ⊤)
    (sourceNativeCoverMap R O p) (sourceNativeCoverMap R O a₀)
    (targetNativeMarked R O z) sO
    (sourceNativeCoverLift_isPullback R O z p s hs H)
    (sourceNativeCoverMap_marked_complement R O a₀ z hz) J d' hdr F
    (restricted_inclusion_toProjectiveLine R p O) ⊤
    (O.toScheme.isoSpec.hom ⟨genericPoint (Spec (.of R)), hηO⟩) (by trivial)

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
