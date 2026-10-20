/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.BaseChange.TwoLocalizationBoundaryFactors
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.BaseChange.TwoLocalizationBoundaryGeometry
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.TwoLocalizationGeometry
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.TwoLocalizationRetainedGeometry
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.FixedThickenedBoundaryAffineAmbients

/-!
# Standard-triple geometry on one fixed twice-localized normalization

The theorem consumes the already selected original whole boundary and exact
localization and ambient witnesses. It never repeats their existential choices.
Closedness, finiteness, full complementary support, disjointness and nonempty
base are proved on the literal native objects. All boundary nilpotents remain.
Smoothness of the base uses the supplied smooth field map, not normality.
The source can be empty, with vacuous fiber-component conditions. Marked-product
line frames and their coherence are separate from this geometric conjunction.

Intended upstream owner: `Aglib.AlgebraicGeometry.Normalization.Compactification`
with leaf `RelativeAffineLine.TwoLocalizationStandardTripleGeometry`.
Current consumer: fixed-witness standard-triple assembly, documented in the
owning normalization guide. The theorem is deterministic, not a new chooser.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

open Scheme.Hom RelativeProjectiveLine
open AlgebraicGeometry.FiniteSchemeNormBaseChange

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] {Y Z : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (z : Z ⟶ Spec (.of (Polynomial R))) [IsClosedImmersion z]
  [IsFinite (z ≫ boundaryLineProjection R)] (s : Z ⟶ Y) (hs : s ≫ p = z)
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
  (a : Γ(O.toScheme, ⊤)) (b : Localization.Away a)

local notation "F₀" => boundaryBaseProjectiveMap R (ULift (Fin 2)) (toProjectiveLine R p) O
local notation "J₀" => boundaryBaseCoverInclusion (boundaryLineProjection R) p (projection R p)
  (inclusion R p) (inclusion_projection R p) ⊤ O
local notation "s₀" => boundaryBaseCoverLift (boundaryLineProjection R) p z s hs ⊤ O
  (fun _ _ => trivial)
local notation "z₀" => s₀ ≫ J₀
local notation "C₂" => TwoLocalizations.source (O.toScheme.presheaf.obj (Opposite.op ⊤)) a b F₀
local notation "ρ" => TwoLocalizations.sourceMap
  (O.toScheme.presheaf.obj (Opposite.op ⊤)) a b F₀
local notation "g₂" => TwoLocalizations.toProjectiveLine
  (O.toScheme.presheaf.obj (Opposite.op ⊤)) a b F₀
local notation "q₂" => TwoLocalizations.projection
  (O.toScheme.presheaf.obj (Opposite.op ⊤)) a b F₀
local notation "Y₂" => TwoLocalizations.retainedSource
  (O.toScheme.presheaf.obj (Opposite.op ⊤)) a b F₀ J₀
local notation "J₂" => TwoLocalizations.retainedInclusion
  (O.toScheme.presheaf.obj (Opposite.op ⊤)) a b F₀ J₀

/-- Geometric standard-triple properties on one fixed twice-localized normalization.
Only the coefficient base is required nonempty; empty sources have vacuous
fiber-component conditions. The original boundary and the final ambient are the
already selected full schemes and open, not desired final-property premises. -/
theorem twoLocalization_standardTriple_geometry
    (x : Spec (.of R)) (hx : x ∈ O) (ha : a ≠ 0) (hb : b ≠ 0)
    (r : R) (hOr : O ≤ PrimeSpectrum.basicOpen r)
    (hfree : ∀ i : ULift.{u} (Fin 2),
      let w := chart (Localization.Away r) i ≫
        ProjectiveSpace.map (algebraMap R (Localization.Away r)) (ULift.{u} (Fin 2))
      let : Algebra (Polynomial (Localization.Away r))
        Γ(pullback (toProjectiveLine R p) w, ⊤) :=
        (scalarMap (pullback.snd (toProjectiveLine R p) w)).toAlgebra
      Module.Free (Polynomial (Localization.Away r)) Γ(pullback (toProjectiveLine R p) w, ⊤))
    (H : IsPullback s (𝟙 Z) p z)
    {D : Scheme.{u}} (d : D ⟶ boundaryBaseCompactification (projection R p) O)
    (hdc : IsClosedImmersion d)
    (hdf : IsFinite (d ≫ (F₀ ≫ ProjectiveSpace.toSpec Γ(O.toScheme, ⊤)
      (ULift.{u} (Fin 2)))))
    (hd : Set.range d = (Set.range J₀)ᶜ)
    (U : (C₂).Opens) (hU : IsAffineOpen U)
    (u : TwoLocalizations.boundary Γ(O.toScheme, ⊤) a b F₀ (coprod.desc d z₀) ⟶ U.toScheme)
    (hu : u ≫ U.ι = TwoLocalizations.boundaryMap Γ(O.toScheme, ⊤) a b F₀ (coprod.desc d z₀))
    {k : Type u} [Field k] (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t] :
    IsFinite g₂ ∧ Flat g₂ ∧ IsProper q₂ ∧ Flat q₂ ∧
      (∀ v : Spec (.of (Localization.Away b)), ∀ W : Set ((q₂).fiber v),
        W ∈ irreducibleComponents ((q₂).fiber v) → topologicalKrullDim W = 1) ∧
      NormalStalks C₂ ∧ IsAffine (Spec (.of (Localization.Away b))) ∧
      Nonempty (Spec (.of (Localization.Away b))) ∧
      Smooth (twoLocalizationFieldMap R O a b t) ∧
      IsOpenImmersion J₂ ∧ SmoothOfRelativeDimension 1 (J₂ ≫ q₂) ∧
      Smooth ((J₂ ≫ q₂) ≫ twoLocalizationFieldMap R O a b t) ∧ (Y₂).IsQuasiAffine ∧
      IsClosedImmersion (pullback.snd d ρ) ∧ IsClosedImmersion (pullback.snd z₀ ρ) ∧
      IsFinite (pullback.snd d ρ ≫ q₂) ∧ IsFinite (pullback.snd z₀ ρ ≫ q₂) ∧
      Set.range (pullback.snd d ρ) = (Set.range J₂)ᶜ ∧
      Disjoint (Set.range (pullback.snd d ρ)) (Set.range (pullback.snd z₀ ρ)) ∧
      IsAffineOpen U ∧
      ∃ (uD : pullback d ρ ⟶ U.toScheme) (uZ : pullback z₀ ρ ⟶ U.toScheme),
        uD ≫ U.ι = pullback.snd d ρ ∧ uZ ≫ U.ι = pullback.snd z₀ ρ := by
  let : Nonempty O.toScheme := ⟨⟨x, hx⟩⟩
  let : IsIntegral O.toScheme := isIntegral_of_isOpenImmersion O.ι
  let : IsDomain Γ(O.toScheme, ⊤) := inferInstance
  let : Flat F₀ := originalCoefficient_projectiveMap_flat R r O hOr (toProjectiveLine R p) hfree
  let : IsClosedImmersion d := hdc
  let : IsFinite (d ≫ (F₀ ≫ ProjectiveSpace.toSpec Γ(O.toScheme, ⊤)
      (ULift.{u} (Fin 2)))) := hdf
  let : IsClosedImmersion s := MorphismProperty.of_isPullback H.flip inferInstance
  let : IsProper ((s ≫ inclusion R p) ≫ projection R p) := by
    rw [Category.assoc, inclusion_projection, ← Category.assoc, hs]
    infer_instance
  let : IsProper (s ≫ inclusion R p) := IsProper.of_comp _ (projection R p)
  let : IsClosedImmersion (s ≫ inclusion R p) :=
    IsClosedImmersion.of_isPreimmersion _ (s ≫ inclusion R p).isClosedMap.isClosed_range
  let : IsClosedImmersion z₀ :=
    boundaryBaseSourceZero_closed (boundaryLineProjection R) p z s hs
      (projection R p) (inclusion R p) (inclusion_projection R p) ⊤ O
      (fun _ _ => trivial)
  let : IsFinite (z₀ ≫ (F₀ ≫ ProjectiveSpace.toSpec Γ(O.toScheme, ⊤)
      (ULift.{u} (Fin 2)))) := by
    rw [boundaryBaseProjectiveMap_toSpec, ← Category.assoc]
    let := boundaryBaseSourceZero_finite (boundaryLineProjection R) p z s hs
      (projection R p) (inclusion R p) (inclusion_projection R p) ⊤ O
      (fun _ _ => trivial)
    infer_instance
  have hdz : Disjoint (Set.range d) (Set.range z₀) := by
    apply Set.disjoint_left.mpr
    rintro _ hxD ⟨y, rfl⟩
    rw [hd] at hxD
    exact hxD ⟨s₀ y, rfl⟩
  refine ⟨inferInstance, inferInstance, inferInstance,
    TwoLocalizations.projection_flat Γ(O.toScheme, ⊤) a b F₀,
    ?_, twoLocalization_normalStalks R p O a b, inferInstance,
    TwoLocalizations.nonempty_base Γ(O.toScheme, ⊤) a b ha hb,
    twoLocalization_base_smooth R O a b t,
    twoLocalization_retained_open R p O a b,
    twoLocalization_retained_smooth R p O a b,
    twoLocalization_retained_field_smooth R p O a b t,
    twoLocalization_retained_quasiAffine R p O a b,
    inferInstance, inferInstance,
    TwoLocalizations.boundary_projection_finite Γ(O.toScheme, ⊤) a b F₀ d,
    TwoLocalizations.boundary_projection_finite Γ(O.toScheme, ⊤) a b F₀ z₀,
    TwoLocalizations.boundary_range_eq_compl Γ(O.toScheme, ⊤) a b F₀ d J₀ hd,
    TwoLocalizations.boundary_disjoint Γ(O.toScheme, ⊤) a b F₀ d z₀ hdz, hU,
    TwoLocalizations.coproductBoundary_factors_through_ambient
      Γ(O.toScheme, ⊤) a b F₀ d z₀ U u hu⟩
  intro v W hW
  exact TwoLocalizations.fiber_component_dimension Γ(O.toScheme, ⊤) a b F₀ v hW

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
