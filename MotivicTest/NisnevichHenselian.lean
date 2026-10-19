/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Henselian

/-!
# Consumers of henselian Nisnevich-local objects

These consumers use arbitrary étale covering members, indexed covering families,
and nonreduced local Artinian bases. They use the actual generated topology.
-/

open CategoryTheory AlgebraicGeometry _root_.AlgebraicGeometry.Nisnevich

universe u

example {R : Type u} [CommRing R] [HenselianLocalRing R]
    {ι : Type u} {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ Spec (.of R))
    (hf : Presieve.ofArrows Y f ∈ precoverage _) :
    ∃ i, ∃ t : Spec (.of R) ⟶ Y i, t ≫ f i = 𝟙 _ := by
  obtain ⟨_, _, ⟨i⟩, t, ht⟩ := exists_section_of_mem_precoverage_of_henselian R hf
  exact ⟨i, t, ht⟩

example {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Sieve (Spec (.of R))} (hS : S ∈ topology _)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) : S f := by
  rw [covering_sieve_eq_top_of_henselian R hS]
  trivial

example {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    (S : Sieve (Spec (.of R))) : S ∈ topology _ ↔ S = ⊤ :=
  mem_topology_iff_of_artinian R S

example {K : Type u} [Field K] (S : Sieve (Spec (.of K))) :
    S ∈ topology _ ↔ S = ⊤ :=
  mem_topology_iff_of_artinian K S

set_option linter.hashCommand false in
#print axioms exists_section_of_mem_precoverage_of_henselian
set_option linter.hashCommand false in
#print axioms exists_section_of_mem_precoverage_of_artinian
set_option linter.hashCommand false in
#print axioms mem_topology_iff_of_henselian
set_option linter.hashCommand false in
#print axioms mem_topology_iff_of_artinian
