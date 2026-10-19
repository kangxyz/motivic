/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Etale.Sections.ArtinianEtaleSections
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Nisnevich lifting on whole scheme-theoretic fibers

An étale morphism with an actual residue-field-isomorphism lift at every point
admits lifts from every locally Artinian scheme. In particular it lifts the
entire scheme-theoretic fiber of a locally quasi-finite morphism, retaining
all its components and nilpotents. This is a lift on the fiber itself;
descent to a neighborhood in the original base is a separate step.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

private theorem exists_field_lift_of_residueFieldIso {U Z : Scheme.{u}} (q : U ⟶ Z)
    (h : ∀ z : Z, ∃ x : U, q x = z ∧ IsIso (q.residueFieldMap x))
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ Z) :
    ∃ b : Spec (.of K) ⟶ U, b ≫ q = a := by
  have hlift : ∀ z : Z, ∃ s : Spec (Z.residueField z) ⟶ U,
      s ≫ q = Z.fromSpecResidueField z := by
    intro z
    obtain ⟨x, rfl, hx⟩ := h z
    let := hx
    refine ⟨Spec.map (inv (q.residueFieldMap x)) ≫ U.fromSpecResidueField x, ?_⟩
    rw [Category.assoc, ← q.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  obtain ⟨s, hs⟩ := hlift (a (IsLocalRing.closedPoint K))
  refine ⟨Spec.map (Z.descResidueField (Scheme.stalkClosedPointTo a)) ≫ s, ?_⟩
  rw [Category.assoc, hs]
  exact Z.descResidueField_stalkClosedPointTo_fromSpecResidueField K a

/-- A pointwise Nisnevich-surjective étale morphism lifts every map from a
locally Artinian scheme, without discarding its nilpotents or components. -/
theorem exists_lift_from_locallyArtinian_of_residueFieldIso
    {U Z A : Scheme.{u}} (q : U ⟶ Z) [Etale q] [IsLocallyArtinian A]
    (h : ∀ z : Z, ∃ x : U, q x = z ∧ IsIso (q.residueFieldMap x)) (a : A ⟶ Z) :
    ∃ b : A ⟶ U, b ≫ q = a := by
  have hlift : ∀ y : A, ∃ s : Spec (A.residueField y) ⟶ pullback q a,
      s ≫ pullback.snd q a = A.fromSpecResidueField y := by
    intro y
    obtain ⟨b, hb⟩ := exists_field_lift_of_residueFieldIso q h
      (A.fromSpecResidueField y ≫ a)
    exact ⟨pullback.lift b (A.fromSpecResidueField y) hb, pullback.lift_snd _ _ _⟩
  obtain ⟨t, ht⟩ := ArtinianEtale.exists_section_of_etale_of_isLocallyArtinian
    (pullback.snd q a) hlift
  refine ⟨t ≫ pullback.fst q a, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]

/-- The entire actual fiber of a locally quasi-finite morphism lifts through
a Nisnevich-surjective étale morphism of its source. -/
theorem exists_lift_from_quasiFiniteFiber_of_residueFieldIso
    {U Z S : Scheme.{u}} (p : Z ⟶ S) [LocallyQuasiFinite p]
    (q : U ⟶ Z) [Etale q]
    (h : ∀ z : Z, ∃ x : U, q x = z ∧ IsIso (q.residueFieldMap x)) (s : S) :
    ∃ b : p.fiber s ⟶ U, b ≫ q = p.fiberι s :=
  exists_lift_from_locallyArtinian_of_residueFieldIso q h (p.fiberι s)

end AlgebraicGeometry.Scheme.Hom
