/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.RestrictedMarkedSquare
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NativeComplement
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.SourceTargetFullAffineAmbients
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.SourceBoundary
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.ZeroNeighborhoodBoundary

/-!
# Full affine-boundary ambients from fixed thickened-boundary witnesses

The affine coefficient open, its retained point, the whole closed boundary,
and its original map are inputs already selected by the caller. The source
and target full boundary maps are the actual disjoint coproduct maps. Their
closedness and finiteness are derived before the existing lower supplier makes
exactly its two coefficient localizations and chooses the two affine opens.

No finite/free localization, normalization, thickening, residual-boundary
factor, section, or frame is chosen here. The complete original hypotheses
and fixed maps are retained in the signatures below. The boundary is not
replaced by its reduction or by the support of an image.

Intended upstream module: `FixedThickenedBoundaryAffineAmbients` in
`Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine`.
Current consumer: `ThickenedBoundaryAffineAmbients`. Fixed-witness callers
can use this theorem without invoking a normalization or boundary chooser.
The supplied point proves nonemptiness of the initial coefficient open; the
conclusion does not assert that it survives the later localizations.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom RelativeProjectiveLine
universe u

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] {Y Z : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (z : Z ⟶ Spec (.of (Polynomial R))) [IsClosedImmersion z]
  [IsFinite (z ≫ boundaryLineProjection R)] (s : Z ⟶ Y) (hs : s ≫ p = z)
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]

local notation "F" => boundaryBaseProjectiveMap R (ULift (Fin 2)) (toProjectiveLine R p) O
local notation "J" => boundaryBaseCoverInclusion (boundaryLineProjection R) p (projection R p)
  (inclusion R p) (inclusion_projection R p) ⊤ O
local notation "sO" => boundaryBaseCoverLift (boundaryLineProjection R) p z s hs ⊤ O
  (fun _ _ => trivial)
local notation "zO" => targetNativeMarked R O z

/-- The supplied whole thickened boundary and the original marked schemes give
closed finite full coproduct boundaries and affine ambients after the exact two
localizations of the existing lower supplier. No prior witness is chosen again. -/
theorem fixedThickenedBoundary_fullBoundary_affineAmbients
    (x : Spec (.of R)) (hx : x ∈ O)
    {D' : Scheme.{u}} (d' : D' ⟶ boundaryBaseCompactification (projection R p) O)
    (hdc : IsClosedImmersion d')
    (hdf : IsFinite (d' ≫ (F ≫
      ProjectiveSpace.toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)))))
    (hds : Disjoint (Set.range (sO ≫ J)) (Set.range d'))
    (H : IsPullback s (𝟙 Z) p z) :
    IsClosedImmersion (coprod.desc d' (sO ≫ J)) ∧
      IsFinite ((coprod.desc d' (sO ≫ J) ≫ F) ≫
        ProjectiveSpace.toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2))) ∧
      IsClosedImmersion (coprod.desc (neighborhoodBoundaryInclusion Γ(O.toScheme, ⊤) ⊤)
        (zO ≫ chart Γ(O.toScheme, ⊤) 0)) ∧
      IsFinite (coprod.desc (neighborhoodBoundaryInclusion Γ(O.toScheme, ⊤) ⊤)
        (zO ≫ chart Γ(O.toScheme, ⊤) 0) ≫
          ProjectiveSpace.toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2))) ∧
      ProjectiveSpace.SourceTargetFullBoundaryAffineAmbients Γ(O.toScheme, ⊤) F
        (coprod.desc d' (sO ≫ J))
        (coprod.desc (neighborhoodBoundaryInclusion Γ(O.toScheme, ⊤) ⊤)
          (zO ≫ chart Γ(O.toScheme, ⊤) 0)) := by
  let S := Γ(O.toScheme, ⊤)
  let π := ProjectiveSpace.toSpec S (ULift.{u} (Fin 2))
  let dA := neighborhoodBoundaryInclusion S ⊤
  let : IsNoetherianRing S :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top O.toScheme⟩
  let : Nonempty O.toScheme := ⟨⟨x, hx⟩⟩
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
  have hsF : (sO ≫ J) ≫ F = zO ≫ chart S 0 := by
    rw [Category.assoc, restricted_inclusion_toProjectiveLine, ← Category.assoc,
      sourceNativeCoverLift_map]
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
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact ProjectiveSpace.exists_source_target_affine_boundary_ambients S
    (ULift.{u} (Fin 2)) 1 Equiv.ulift F
    (coprod.desc d' (sO ≫ J)) (coprod.desc dA (zO ≫ chart S 0))

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
