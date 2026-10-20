/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.BaseChange.TwoLocalizationRetained
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.FlatStructure
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Geometry of full boundaries after the two literal localizations

The same native source and its direct full-boundary pullbacks retain finiteness,
complementary support and disjointness. The projection is flat when the original
projective map is flat. Only the coefficient-base nonemptiness theorem assumes
a domain and two nonzero localization elements. No source nonemptiness is needed.

Intended upstream owner: `Aglib.AlgebraicGeometry.ProjectiveLine.BaseChange`
with leaf `TwoLocalizationBoundaryGeometry`.
Current consumer: `Normalization.Compactification.RelativeAffineLine`
with leaf `TwoLocalizationStandardTripleGeometry`, under the candidate root.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RelativeProjectiveLine.TwoLocalizations

variable (R : Type u) [CommRing R] (r : R) (s : Localization.Away r)
  {C : Scheme.{u}} (F : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))

/-- The curve projection is flat by composition, not from properness or dimension. -/
theorem projection_flat [Flat F] : Flat (projection R r s F) := by
  let : Flat (ProjectiveSpace.toSpec (Localization.Away s) (ULift.{u} (Fin 2))) :=
    RelativeProjectiveLine.toSpec_flat (Localization.Away s)
  dsimp only [projection]
  infer_instance

/-- Finiteness of a whole boundary over the base survives the actual pasted square. -/
theorem boundary_projection_finite {D : Scheme.{u}} (d : D ⟶ C)
    [IsFinite (d ≫ (F ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))] :
    IsFinite (pullback.snd d (sourceMap R r s F) ≫ projection R r s F) :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback d (sourceMap R r s F)).paste_vert (baseSquare R r s F))
    inferInstance

/-- The whole boundary's support remains exactly the complement of the retained open. -/
theorem boundary_range_eq_compl {D Y : Scheme.{u}} (d : D ⟶ C) (j : Y ⟶ C)
    (hd : Set.range d = (Set.range j)ᶜ) :
    Set.range (pullback.snd d (sourceMap R r s F)) =
      (Set.range (retainedInclusion R r s F j))ᶜ := by
  rw [Scheme.Pullback.range_snd, hd]
  change (sourceMap R r s F) ⁻¹' (Set.range j)ᶜ =
    (Set.range (pullback.snd j (sourceMap R r s F)))ᶜ
  rw [Scheme.Pullback.range_snd]
  rfl

/-- Disjointness is transported by preimage without reducing either boundary. -/
theorem boundary_disjoint {D Z : Scheme.{u}} (d : D ⟶ C) (z : Z ⟶ C)
    (hdz : Disjoint (Set.range d) (Set.range z)) :
    Disjoint (Set.range (pullback.snd d (sourceMap R r s F)))
      (Set.range (pullback.snd z (sourceMap R r s F))) := by
  rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd]
  exact Set.disjoint_left.mpr fun _ hd hz => Set.disjoint_left.mp hdz hd hz

/-- Two nonzero localizations of the integral coefficient base remain nonempty. -/
theorem nonempty_base [IsDomain R] (hr : r ≠ 0) (hs : s ≠ 0) :
    Nonempty (Spec (.of (Localization.Away s))) := by
  let : IsDomain (Localization.Away r) := Localization.Away.isDomain hr
  let : IsDomain (Localization.Away s) := Localization.Away.isDomain hs
  infer_instance

end AlgebraicGeometry.RelativeProjectiveLine.TwoLocalizations
