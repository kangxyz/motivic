/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NormalizedBoundaryChoice
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NativeComplement
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.SourceTargetBoundaryAffineNeighborhood
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.SourceBoundary
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.ZeroNeighborhoodBoundary

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

namespace AlgebraicGeometry.ProjectiveSpace

/-- The literal two-localization output of the source/target ambient supplier.
The boundary inputs are whole closed schemes, not reduced supports. -/
def SourceTargetFullBoundaryAffineAmbients
    (R : Type u) [CommRing R] {C B Z : Scheme.{u}}
    (f : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) (b : B ⟶ C)
    (z : Z ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) : Prop :=
    ∃ r : R, r ≠ 0 ∧
      let S := Localization.Away r
      let m₁ := ProjectiveSpace.map (algebraMap R S) (ULift.{u} (Fin 2))
      let f₁ := pullback.snd f m₁
      let b₁ : pullback (b ≫ f) m₁ ⟶ pullback f m₁ :=
        pullback.lift (pullback.fst (b ≫ f) m₁ ≫ b)
          (pullback.snd (b ≫ f) m₁) (by simp [Category.assoc, pullback.condition])
      let z₁ := pullback.snd z m₁
      ∃ s : S, s ≠ 0 ∧
        let m₂ := ProjectiveSpace.map (algebraMap S (Localization.Away s))
          (ULift.{u} (Fin 2))
        let t₂ := pullback.fst (𝟙 (ProjectiveSpace S (ULift.{u} (Fin 2)))) m₂
        let c₂ := pullback.fst f₁ t₂
        let z₂ := pullback.lift (pullback.fst (z₁ ≫ 𝟙 _) m₂ ≫ z₁)
          (pullback.snd (z₁ ≫ 𝟙 _) m₂) (by
            simpa only [Category.assoc, Category.comp_id] using
              (pullback.condition (f := z₁ ≫ 𝟙 _) (g := m₂)))
        ∃ U : (pullback f₁ t₂).Opens,
          ∃ V : (pullback (𝟙 (ProjectiveSpace S (ULift.{u} (Fin 2)))) m₂).Opens,
            IsAffineOpen U ∧ IsAffineOpen V ∧
            (∃ u : pullback b₁ c₂ ⟶ U.toScheme,
              u ≫ U.ι = pullback.snd b₁ c₂) ∧
            (∃ v : pullback (z₁ ≫ 𝟙 _) m₂ ⟶ V.toScheme, v ≫ V.ι = z₂)

end AlgebraicGeometry.ProjectiveSpace

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
  let S := Γ(O.toScheme, ⊤)
  let F := boundaryBaseProjectiveMap R (ULift (Fin 2)) (toProjectiveLine R p) O
  let J := boundaryBaseCoverInclusion (boundaryLineProjection R) p (projection R p)
    (inclusion R p) (inclusion_projection R p) ⊤ O
  let sO := boundaryBaseCoverLift (boundaryLineProjection R) p z s hs ⊤ O
    (fun _ _ => trivial)
  let zO := targetNativeMarked R O z
  let dA := neighborhoodBoundaryInclusion S ⊤
  let π := ProjectiveSpace.toSpec S (ULift.{u} (Fin 2))
  let : IsNoetherianRing S :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top O.toScheme⟩
  let : Nonempty O.toScheme := ⟨⟨genericPoint (Spec (.of R)), hηO⟩⟩
  let : IsIntegral O.toScheme := isIntegral_of_isOpenImmersion O.ι
  let : IsDomain S := inferInstance
  let : IsClosedImmersion d' := hdc
  let : IsFinite (d' ≫ (F ≫ π)) := hdf
  let : IsClosedImmersion s := MorphismProperty.of_isPullback H.flip inferInstance
  let : IsProper ((s ≫ inclusion R p) ≫ projection R p) := by
    rw [Category.assoc, inclusion_projection, ← Category.assoc, hs]
    infer_instance
  let : IsProper (s ≫ inclusion R p) := IsProper.of_comp _ (projection R p)
  let : IsClosedImmersion (s ≫ inclusion R p) :=
    IsClosedImmersion.of_isPreimmersion _ (s ≫ inclusion R p).isClosedMap.isClosed_range
  let : IsClosedImmersion (sO ≫ J) :=
    boundaryBaseSourceZero_closed (boundaryLineProjection R) p z s hs
      (projection R p) (inclusion R p) (inclusion_projection R p) ⊤ O
      (fun _ _ => trivial)
  have hsF : (sO ≫ J) ≫ F = zO ≫ chart S 0 :=
    restricted_marked_toProjectiveLine R p O z s hs
  let : IsFinite ((sO ≫ J) ≫ (F ≫ π)) := by
    rw [← Category.assoc, hsF, Category.assoc, chart_toSpec]
    infer_instance
  let : IsClosedImmersion (coprod.desc d' (sO ≫ J)) :=
    isClosedImmersion_coprod_desc d' (sO ≫ J) hds.symm
  let : IsFinite ((coprod.desc d' (sO ≫ J) ≫ F) ≫ π) := by
    rw [Category.assoc, coprod.desc_comp]
    infer_instance
  let : IsProper ((zO ≫ chart S 0) ≫ π) := by
    rw [Category.assoc, chart_toSpec]
    infer_instance
  let : IsProper (zO ≫ chart S 0) := IsProper.of_comp _ π
  let : IsClosedImmersion (zO ≫ chart S 0) :=
    IsClosedImmersion.of_isPreimmersion _ (zO ≫ chart S 0).isClosedMap.isClosed_range
  let : IsFinite (dA ≫ π) := neighborhoodBoundary_finite S ⊤ (by intro y hy; trivial)
  have hdA : Disjoint (Set.range dA) (Set.range (zO ≫ chart S 0)) := by
    rw [show dA = neighborhoodBoundaryInclusion S ⊤ from rfl,
      range_neighborhoodBoundaryInclusion]
    apply Set.disjoint_left.mpr
    rintro _ hx ⟨y, rfl⟩
    exact hx ⟨zO y, trivial, rfl⟩
  let : IsClosedImmersion (coprod.desc dA (zO ≫ chart S 0)) :=
    isClosedImmersion_coprod_desc dA (zO ≫ chart S 0) hdA
  let : IsFinite ((zO ≫ chart S 0) ≫ π) := by
    rw [Category.assoc, chart_toSpec]
    infer_instance
  let : IsFinite (coprod.desc dA (zO ≫ chart S 0) ≫ π) := by
    rw [coprod.desc_comp]
    infer_instance
  refine ⟨r, hr, hfree, O, hO, hηO, hOr, D', d', hdc, hdr, hdj, hds,
    hdf, a, b, c, ha, hb, hc, ?_⟩
  exact ProjectiveSpace.exists_source_target_affine_boundary_ambients S
    (ULift.{u} (Fin 2)) 1 Equiv.ulift F
    (coprod.desc d' (sO ≫ J)) (coprod.desc dA (zO ≫ chart S 0))

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
