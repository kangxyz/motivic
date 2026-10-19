/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.NativeSectionChoice
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.ZeroNeighborhoodBoundary
/-! # Choose sections on the original overlap, not on a boundary neighborhood

The source Serre open is the original affine overlap and the target Serre open
is the original affine puncture. The entire thickened boundary is retained.
Only the coefficient restriction made by the common frame constructor remains.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.OriginalOverlapSectionChoice`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`RelativeAffineLine.OriginalSectionChoice`, `Pencils.NativeOriginalRestrictionActions`,
`MotivicTest.OriginalOverlapSectionChoice`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom RelativeProjectiveLine ProjectiveSpace
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  {Y A Z C D : Scheme.{u}} [IsAffine Y] [IsAffine A]
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p]
  (a : A ⟶ Spec (.of (Polynomial R))) [IsOpenImmersion a]
  (z : Z ⟶ Spec (.of (Polynomial R))) [IsClosedImmersion z]
  (s : Z ⟶ Y) (H : IsPullback s (𝟙 Z) p z)
  (hz : Set.range z = (Set.range a)ᶜ)
  (j : Y ⟶ C) [IsOpenImmersion j] (d : D ⟶ C)
  (hd : Set.range d = (Set.range j)ᶜ)

include H hz hd in
omit [IsNoetherianRing R] [IsAffine Y] [IsAffine A] [Etale p]
  [IsOpenImmersion a] [IsClosedImmersion z] [IsOpenImmersion j] in
/-- The original overlap and the two full boundary components cover the compactification. -/
theorem originalOverlap_boundary_cover (c : C) :
    c ∈ Set.range (pullback.fst p a ≫ j) ∨
      c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j) := by
  classical
  by_cases hc : c ∈ Set.range j
  · obtain ⟨y, rfl⟩ := hc
    by_cases hy : p y ∈ Set.range a
    · left
      have hy' : y ∈ Set.range (pullback.fst p a) := by
        rw [Scheme.Pullback.range_fst]
        exact hy
      obtain ⟨b, rfl⟩ := hy'
      exact ⟨b, rfl⟩
    · right; right
      have hy' : p y ∈ Set.range z := by rwa [hz]
      obtain ⟨w, hw⟩ := hy'
      obtain ⟨b, hb, _⟩ := Scheme.exists_preimage_of_isPullback H y w hw.symm
      exact ⟨b, congrArg j hb⟩
  · right; left
    rwa [hd]

include hz in
omit [IsNoetherianRing R] [IsAffine A] [IsOpenImmersion a] [IsClosedImmersion z] in
/-- The original monic open is the target Serre open; no affine boundary open is needed. -/
theorem originalPuncture_boundary_cover (x : ProjectiveSpace R (ULift.{u} (Fin 2))) :
    x ∈ Set.range (a ≫ chart R 0) ∨
      x ∈ Set.range (neighborhoodBoundaryInclusion R ⊤) ∨
      x ∈ Set.range (z ≫ chart R 0) := by
  classical
  by_cases hx : x ∈ Set.range (chart R 0)
  · obtain ⟨y, rfl⟩ := hx
    by_cases hy : y ∈ Set.range a
    · obtain ⟨b, rfl⟩ := hy
      exact Or.inl ⟨b, rfl⟩
    · have hy' : y ∈ Set.range z := by rwa [hz]
      obtain ⟨b, rfl⟩ := hy'
      exact Or.inr (Or.inr ⟨b, rfl⟩)
  · right; left
    rw [range_neighborhoodBoundaryInclusion]
    rintro ⟨y, _, hy⟩
    exact hx ⟨y, hy⟩

variable [IsClosedImmersion d] [IsClosedImmersion (s ≫ j)]
  [IsFinite (z ≫ boundaryLineProjection R)]
  (f : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsFinite f]
  (hj : j ≫ f = p ≫ chart R 0)
  [IsFinite (d ≫ (f ≫ toSpec R (ULift.{u} (Fin 2))))]

/-- A single common coefficient restriction and the two section choices on fixed geometry. -/
def OriginalOverlapCommonSections
    (W : (Spec (.of R)).Opens) (x : Spec (.of R)) : Prop :=
    ∃ (O : (Spec (.of R)).Opens) (hO : IsAffineOpen O),
      let : IsAffine O.toScheme := hO
      x ∈ O ∧ O ≤ W ∧
      ∃ (hq : j ≫ (f ≫ toSpec R (ULift.{u} (Fin 2))) = p ≫ boundaryLineProjection R)
        (hs : s ≫ p = z),
        NativeSourceBoundarySections (R := R) (ι := ULift.{u} (Fin 2))
          (p := p) (a := a) (f := f) (j := j) (hj := hq)
          (z := z) (s := s) (hs := hs) (H := H) (d := d) (V := O) ∧
        NativeTargetBoundarySections (R := R) (z := z) (V := O)
          (d₀ := neighborhoodBoundaryInclusion R ⊤)
          (hd₀ := by
            rw [range_neighborhoodBoundaryInclusion]
            apply Set.disjoint_left.mpr
            rintro _ ⟨y, rfl⟩ h
            exact h ⟨y, trivial, rfl⟩)
          (v₀ := a ≫ chart R 0)

include H hz hd hj in
/-- Instantiate the common chooser with the original overlap and puncture, retaining
one source section datum and one target pair. No affine neighborhood of the boundary
and no replacement of the original finite map is used. -/
theorem exists_originalOverlap_common_boundary_sections
    (W : (Spec (.of R)).Opens) (x : Spec (.of R)) (hx : x ∈ W) :
    OriginalOverlapCommonSections R p a z s H j d f W x := by
  have hq : j ≫ (f ≫ toSpec R (ULift.{u} (Fin 2))) =
      p ≫ boundaryLineProjection R := by
    rw [← Category.assoc, hj, Category.assoc, chart_toSpec]
  have hs : s ≫ p = z := by simpa only [Category.id_comp] using H.w
  have ha : Disjoint (Set.range a) (Set.range z) := by rw [hz]; exact disjoint_compl_right
  have hd' : Disjoint (Set.range j) (Set.range d) := by rw [hd]; exact disjoint_compl_right
  have hi : Disjoint (Set.range (chart R 0))
      (Set.range (neighborhoodBoundaryInclusion R ⊤)) := by
    rw [range_neighborhoodBoundaryInclusion]
    apply Set.disjoint_left.mpr
    rintro _ ⟨y, rfl⟩ h
    exact h ⟨y, trivial, rfl⟩
  have : IsFinite (neighborhoodBoundaryInclusion R ⊤ ≫ toSpec R (ULift.{u} (Fin 2))) :=
    neighborhoodBoundary_finite R ⊤ (by intro y hy; trivial)
  have : IsProper ((z ≫ chart R 0) ≫ toSpec R (ULift.{u} (Fin 2))) := by
    rw [Category.assoc, chart_toSpec]
    infer_instance
  have : IsProper (z ≫ chart R 0) := IsProper.of_comp _ (toSpec R (ULift.{u} (Fin 2)))
  have : IsClosedImmersion (z ≫ chart R 0) :=
    IsClosedImmersion.of_isPreimmersion _ (z ≫ chart R 0).isClosedMap.isClosed_range
  have : SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
    Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R
  have : SmoothOfRelativeDimension 1
      ((pullback.fst p a ≫ j) ≫ (f ≫ toSpec R (ULift.{u} (Fin 2)))) := by
    rw [Category.assoc, hq, ← Category.assoc]
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)
  have : SmoothOfRelativeDimension 1
      ((a ≫ chart R 0) ≫ ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2)))) := by
    simp only [Category.id_comp, Category.assoc, chart_toSpec]
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)
  obtain ⟨O, hO, hxO, hOW, hsource, htarget⟩ :=
    exists_common_native_boundary_sections
      (R := R) (ι := ULift.{u} (Fin 2)) (m := 1) (eι := Equiv.ulift)
      (p := p) (a := a) (f := f) (j := j) (hj := hq)
      (z := z) (s := s) (hs := hs) (H := H) (ha := ha)
      (d := d) (hd := hd') (v := pullback.fst p a ≫ j)
      (hc := originalOverlap_boundary_cover R p a z s H hz j d hd)
      (d₀ := neighborhoodBoundaryInclusion R ⊤) (hd₀ := hi)
      (v₀ := a ≫ chart R 0) (hc₀ := originalPuncture_boundary_cover R a z hz) W x hx
  exact ⟨O, hO, hxO, hOW, hq, hs, hsource, htarget⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
