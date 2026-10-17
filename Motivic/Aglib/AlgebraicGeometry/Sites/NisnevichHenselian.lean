/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.HenselianEtaleSections
public import Motivic.AlgebraicGeometry.Sites.Nisnevich

/-!
# Nisnevich covers of henselian local schemes

A Nisnevich family over the spectrum of a henselian local ring contains a
morphism with a section. The section is obtained by lifting the family's
actual residue-field point through its étale member. Consequently every
covering sieve at this object is maximal. Local Artinian rings are included
without a reducedness assumption.

This is a local-object statement for the actual big Nisnevich topology. It
does not assert that a covering family has a globally split member over a
nonlocal Artinian base, nor that sheafification preserves transfers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace Motivic.Nisnevich

/-- A Nisnevich family over a henselian local ring contains a split member. -/
theorem exists_section_of_mem_precoverage_of_henselian
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {P : Presieve (Spec (.of R))} (hP : P ∈ precoverage _) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of R)), P f ∧
      ∃ t : Spec (.of R) ⟶ Y, t ≫ f = 𝟙 _ := by
  obtain ⟨Y, f, hf, s, hs⟩ := mem_fieldLiftingPrecoverage_iff.mp hP.2
    (ResidueField R) (Spec.map (CommRingCat.ofHom (residue R)))
  have : Etale f := (mem_precoverage_iff.mp hP).1 f hf
  obtain ⟨t, ht, _⟩ := HenselianEtale.exists_section_of_etale f s hs
  exact ⟨Y, f, hf, t, ht⟩

/-- The same section statement holds over a possibly nonreduced local Artinian ring. -/
theorem exists_section_of_mem_precoverage_of_artinian
    (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    {P : Presieve (Spec (.of R))} (hP : P ∈ precoverage _) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of R)), P f ∧
      ∃ t : Spec (.of R) ⟶ Y, t ≫ f = 𝟙 _ := by
  obtain ⟨Y, f, hf, s, hs⟩ := mem_fieldLiftingPrecoverage_iff.mp hP.2
    (ResidueField R) (Spec.map (CommRingCat.ofHom (residue R)))
  have : Etale f := (mem_precoverage_iff.mp hP).1 f hf
  obtain ⟨t, ht, _⟩ := HenselianEtale.exists_section_of_etale_of_artinian f s hs
  exact ⟨Y, f, hf, t, ht⟩

/-- A henselian local spectrum has no nonmaximal Nisnevich covering sieve. -/
theorem covering_sieve_eq_top_of_henselian
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {S : Sieve (Spec (.of R))} (hS : S ∈ topology _) : S = ⊤ := by
  obtain ⟨P, hP, hPS⟩ :=
    precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hS
  obtain ⟨Y, f, hf, t, ht⟩ := exists_section_of_mem_precoverage_of_henselian R hP
  apply Sieve.id_mem_iff_eq_top.mp
  simpa only [ht] using S.downward_closed (hPS _ _ hf) t

/-- A local Artinian spectrum is a local object for the actual Nisnevich topology. -/
theorem covering_sieve_eq_top_of_artinian
    (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    {S : Sieve (Spec (.of R))} (hS : S ∈ topology _) : S = ⊤ := by
  obtain ⟨P, hP, hPS⟩ :=
    precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hS
  obtain ⟨Y, f, hf, t, ht⟩ := exists_section_of_mem_precoverage_of_artinian R hP
  apply Sieve.id_mem_iff_eq_top.mp
  simpa only [ht] using S.downward_closed (hPS _ _ hf) t

/-- Exact membership criterion at a henselian local spectrum. -/
theorem mem_topology_iff_of_henselian
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S : Sieve (Spec (.of R))) : S ∈ topology _ ↔ S = ⊤ :=
  ⟨covering_sieve_eq_top_of_henselian R, fun h ↦ h ▸ topology.top_mem _⟩

/-- Exact membership criterion at a local Artinian spectrum. -/
theorem mem_topology_iff_of_artinian
    (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    (S : Sieve (Spec (.of R))) : S ∈ topology _ ↔ S = ⊤ :=
  ⟨covering_sieve_eq_top_of_artinian R, fun h ↦ h ▸ topology.top_mem _⟩

end Motivic.Nisnevich
