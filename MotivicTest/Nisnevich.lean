/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Evaluation

/-!
# Consumers of the Nisnevich site and exact field evaluation

These tests exercise the actual topology, residue-field criterion, split
covers, and exact abelian evaluation. They do not assume analogous statements
for the étale topology.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Nisnevich

universe u

example (K : Type u) [Field K] :
    Presieve.singleton (𝟙 (Spec (.of K))) ∈ precoverage _ :=
  Precoverage.mem_coverings_of_isIso _

example (K : Type u) [Field K] (R : Presieve (Spec (.of K)))
    (hR : R ∈ precoverage _) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of K)), R f ∧
      ∃ s : Spec (.of K) ⟶ Y, s ≫ f = 𝟙 _ :=
  exists_section_of_mem_precoverage K hR

example (K : Type u) [Field K] (S : Sieve (Spec (.of K))) :
    S ∈ topology _ ↔ S = ⊤ := mem_topology_iff K S

example (X : Scheme.{u}) (ι : Type u) (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (he : ∀ i, Etale (f i))
    (hl : ∀ x : X, ∃ (i : ι) (y : Y i), f i y = x ∧ IsIso ((f i).residueFieldMap y)) :
    Presieve.ofArrows Y f ∈ precoverage X :=
  (ofArrows_mem_precoverage_iff f).mpr ⟨he, hl⟩

example (K : Type u) [Field K]
    {F G : Sheaf topology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [Epi φ] :
    Epi ((evaluation K).map φ) := inferInstance

example (K : Type u) [Field K]
    (S : ShortComplex (Sheaf topology AddCommGrpCat.{u + 1})) (hS : S.Exact) :
    (S.map (evaluation K)).Exact := exact_map_evaluation K S hS

#print axioms mem_fieldLiftingPrecoverage_iff_residueField
#print axioms mem_topology_iff
#print axioms surjective_app_of_epi
#print axioms exact_map_evaluation
