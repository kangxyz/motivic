/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.HenselianEtaleSections

/-!
# Consumers of henselian étale scheme sections

The consumers below use an arbitrary scheme, check both section and prescribed
reduction, and extract equality on the underlying points. They also specialize
to open immersions and to local Artinian bases without reducedness hypotheses.
The affine consumer checks the bridge from an étale algebra and its residue
point to a scheme section.
-/

open CategoryTheory AlgebraicGeometry IsLocalRing Motivic.HenselianEtale

universe u

example {R : Type u} [CommRing R] [HenselianLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [Etale f]
    (s : Spec (.of (ResidueField R)) ⟶ X)
    (hs : s ≫ f = Spec.map (CommRingCat.ofHom (residue R))) :
    ∃ t : Spec (.of R) ⟶ X,
      t ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (residue R)) ≫ t = s :=
  exists_section_of_etale f s hs

example {R : Type u} [CommRing R] [HenselianLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [Etale f]
    (s : Spec (.of (ResidueField R)) ⟶ X)
    (hs : s ≫ f = Spec.map (CommRingCat.ofHom (residue R))) :
    ∃ t : Spec (.of R) ⟶ X,
      (∀ x, f (t x) = x) ∧
      t (Spec.map (CommRingCat.ofHom (residue R)) default) = s default := by
  obtain ⟨t, ht, hres⟩ := exists_section_of_etale f s hs
  exact ⟨t, fun x ↦ congr($ht x), congr($hres default)⟩

example {R : Type u} [CommRing R] [HenselianLocalRing R] {X : Scheme.{u}}
    (j : X ⟶ Spec (.of R)) [IsOpenImmersion j]
    (s : Spec (.of (ResidueField R)) ⟶ X)
    (hs : s ≫ j = Spec.map (CommRingCat.ofHom (residue R))) :
    ∃ t : Spec (.of R) ⟶ X,
      t ≫ j = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (residue R)) ≫ t = s :=
  exists_section_of_etale j s hs

example {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Etale f]
    (s : Spec (.of (ResidueField R)) ⟶ X)
    (hs : s ≫ f = Spec.map (CommRingCat.ofHom (residue R))) :
    ∃ t : Spec (.of R) ⟶ X,
      t ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (residue R)) ≫ t = s :=
  exists_section_of_etale_of_artinian f s hs

example {R B : Type u} [CommRing R] [CommRing B] [HenselianLocalRing R]
    [Algebra R B] [Algebra.Etale R B] (φ : B →ₐ[R] ResidueField R) :
    ∃ t : Spec (.of R) ⟶ Spec (.of B),
      t ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (residue R)) ≫ t =
        Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      ((RingHom.etale_algebraMap).mpr inferInstance)
  apply exists_section_of_etale
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact φ.commutes r

set_option linter.hashCommand false in
#print axioms Motivic.HenselianEtale.exists_section_of_etale
set_option linter.hashCommand false in
#print axioms Motivic.HenselianEtale.exists_section_of_etale_of_artinian
