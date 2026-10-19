/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Etale.Sections.ArtinianEtaleSections
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers of whole-Artinian scheme sections

These consumers permit arbitrary étale source schemes, work over every
component of a nonreduced nonlocal base, and include the empty zero-ring base.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Hom.ArtinianEtale

universe u

namespace Motivic.MotivicTest.ArtinianSchemeSections

example {R : Type u} [CommRing R] [IsArtinianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [Etale f]
    (h : ∀ y : Spec (.of R), ∃ s : Spec ((Spec (.of R)).residueField y) ⟶ X,
      s ≫ f = (Spec (.of R)).fromSpecResidueField y) :
    ∃ t : Spec (.of R) ⟶ X, t ≫ f = 𝟙 _ ∧ ∀ y, f (t y) = y := by
  obtain ⟨t, ht⟩ := exists_section_of_etale_of_artinian f h
  exact ⟨t, ht, fun y ↦ congr($ht y)⟩

example {X Y : Scheme.{u}} [IsArtinianScheme Y] (f : X ⟶ Y) [Etale f]
    (h : ∀ y : Y, ∃ s : Spec (Y.residueField y) ⟶ X,
      s ≫ f = Y.fromSpecResidueField y) :
    ∃ t : Y ⟶ X, t ≫ f = 𝟙 _ :=
  exists_section_of_etale_of_isLocallyArtinian f h

/-- The source is arbitrary; the entire two-component nilpotent base splits. -/
theorem nonreduced_twoComponent_section {X : Scheme.{0}}
    (f : X ⟶ Spec (.of (ZMod 4 × ZMod 4))) [Etale f]
    (h : ∀ y : Spec (.of (ZMod 4 × ZMod 4)),
      ∃ s : Spec ((Spec (.of (ZMod 4 × ZMod 4))).residueField y) ⟶ X,
        s ≫ f = (Spec (.of (ZMod 4 × ZMod 4))).fromSpecResidueField y) :
    ∃ t : Spec (.of (ZMod 4 × ZMod 4)) ⟶ X, t ≫ f = 𝟙 _ := by
  have : IsArtinianRing (ZMod 4 × ZMod 4) := isArtinian_of_finite
  exact exists_section_of_etale_of_artinian f h

/-- For the zero base ring the rational-lift condition is vacuous. -/
theorem zeroRing_section {X : Scheme.{0}} (f : X ⟶ Spec (.of (ZMod 1))) [Etale f] :
    ∃ t : Spec (.of (ZMod 1)) ⟶ X, t ≫ f = 𝟙 _ := by
  have : IsArtinianRing (ZMod 1) := isArtinian_of_finite
  have : IsEmpty (Spec (.of (ZMod 1))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum (ZMod 1)))
  exact exists_section_of_etale_of_artinian f (fun y ↦ isEmptyElim y)

example {X Y : Scheme.{u}} [IsLocallyArtinian Y] (j : X ⟶ Y) [IsOpenImmersion j]
    (h : ∀ y : Y, ∃ s : Spec (Y.residueField y) ⟶ X,
      s ≫ j = Y.fromSpecResidueField y) :
    ∃ t : Y ⟶ X, t ≫ j = 𝟙 _ :=
  exists_section_of_etale_of_isLocallyArtinian j h

/-- The usual point-and-residue-isomorphism condition supplies genuine rational lifts. -/
theorem section_of_residueField_isomorphisms {X Y : Scheme.{u}} [IsLocallyArtinian Y]
    (f : X ⟶ Y) [Etale f]
    (h : ∀ y : Y, ∃ x : X, f x = y ∧ IsIso (f.residueFieldMap x)) :
    ∃ t : Y ⟶ X, t ≫ f = 𝟙 _ := by
  apply exists_section_of_etale_of_isLocallyArtinian f
  intro y
  obtain ⟨x, rfl, hx⟩ := h y
  let := hx
  refine ⟨Spec.map (inv (f.residueFieldMap x)) ≫ X.fromSpecResidueField x, ?_⟩
  rw [Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]

set_option linter.hashCommand false in
#print axioms exists_section_of_etale_of_isLocallyArtinian
set_option linter.hashCommand false in
#print axioms exists_section_of_etale_of_artinian
set_option linter.hashCommand false in
#print axioms Motivic.MotivicTest.ArtinianSchemeSections.nonreduced_twoComponent_section
set_option linter.hashCommand false in
#print axioms Motivic.MotivicTest.ArtinianSchemeSections.zeroRing_section

set_option linter.hashCommand false in
#print axioms Motivic.MotivicTest.ArtinianSchemeSections.section_of_residueField_isomorphisms

end Motivic.MotivicTest.ArtinianSchemeSections
