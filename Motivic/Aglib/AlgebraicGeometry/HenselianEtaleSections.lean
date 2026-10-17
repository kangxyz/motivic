/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.HenselianEtaleSections
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Residue-compatible sections of étale schemes over henselian local rings

A residue-field point of an arbitrary étale scheme over a henselian local ring
lifts to a section with that prescribed reduction. The total scheme need not
be affine: an affine open neighborhood of the given point suffices to apply
the algebraic lifting theorem. The same statement holds for local Artinian
rings, without a reducedness assumption.

This is the scheme form of the henselian étale lifting property in
[Stacks Project, Tag 04GE](https://stacks.math.columbia.edu/tag/04GE).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace Motivic.HenselianEtale

private theorem exists_section_of_etale_of_exists_lift
    {R : Type u} [CommRing R] [IsLocalRing R]
    (hlift : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.Etale R B]
      (φ : B →ₐ[R] ResidueField R), ∃ ψ : B →ₐ[R] R,
        (IsScalarTower.toAlgHom R R (ResidueField R)).comp ψ = φ)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Etale f]
    (s : Spec (.of (ResidueField R)) ⟶ X)
    (hs : s ≫ f = Spec.map (CommRingCat.ofHom (residue R))) :
    ∃ t : Spec (.of R) ⟶ X,
      t ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (residue R)) ≫ t = s := by
  obtain ⟨B, j, hj, hmem, _⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := s default) (U := ⊤) (by simp)
  let := hj
  have hrange : Set.range s ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    rwa [Subsingleton.elim x default]
  let s' := IsOpenImmersion.lift j s hrange
  have hs' : s' ≫ j = s := IsOpenImmersion.lift_fac j s hrange
  let a := Spec.preimage (j ≫ f)
  have ha : a.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp (by
    simpa only [a, Spec.map_preimage] using inferInstanceAs (Etale (j ≫ f)))
  let : Algebra R B := a.hom.toAlgebra
  let : Algebra.Etale R B := ha
  have hφ : a ≫ Spec.preimage s' = CommRingCat.ofHom (residue R) := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, a, Spec.map_preimage, ← Category.assoc, hs'] using hs
  let φ : B →ₐ[R] ResidueField R :=
    { (Spec.preimage s').hom with commutes' := fun r ↦ congr($hφ r) }
  obtain ⟨ψ, hψ⟩ := hlift B φ
  have hψa : a ≫ CommRingCat.ofHom ψ.toRingHom = 𝟙 (CommRingCat.of R) := by
    ext r
    exact ψ.commutes r
  have hres : CommRingCat.ofHom ψ.toRingHom ≫ CommRingCat.ofHom (residue R) =
      Spec.preimage s' := by
    ext b
    exact DFunLike.congr_fun hψ b
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ j, ?_, ?_⟩
  · rw [Category.assoc, ← Spec.map_preimage (j ≫ f), ← Spec.map_comp, hψa, Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, hres, Spec.map_preimage, hs']

/-- A residue-field point of any étale scheme over a henselian local ring lifts
to a section, with precisely the prescribed residue-field reduction. -/
theorem exists_section_of_etale {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Etale f]
    (s : Spec (.of (ResidueField R)) ⟶ X)
    (hs : s ≫ f = Spec.map (CommRingCat.ofHom (residue R))) :
    ∃ t : Spec (.of R) ⟶ X,
      t ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (residue R)) ≫ t = s :=
  exists_section_of_etale_of_exists_lift
    (fun _ _ _ _ ↦ exists_lift_of_etale) f s hs

/-- A residue-field point of any étale scheme over a local Artinian ring lifts
to a section with the given reduction. The base ring need not be reduced. -/
theorem exists_section_of_etale_of_artinian {R : Type u} [CommRing R]
    [IsLocalRing R] [IsArtinianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Etale f]
    (s : Spec (.of (ResidueField R)) ⟶ X)
    (hs : s ≫ f = Spec.map (CommRingCat.ofHom (residue R))) :
    ∃ t : Spec (.of R) ⟶ X,
      t ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (residue R)) ≫ t = s :=
  exists_section_of_etale_of_exists_lift
    (fun _ _ _ _ ↦ exists_lift_of_etale_of_artinian) f s hs

end Motivic.HenselianEtale
