/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.NisnevichFiniteSubfamily
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers of noetherian finite Nisnevich subfamilies

The tests keep the indexing universe independent of the scheme universe,
retain actual residue-field isomorphisms, include the empty scheme and empty
indexing type, and specialize to fields and the nonreduced ring `ZMod 4`.
-/

open CategoryTheory AlgebraicGeometry Motivic.Nisnevich

universe u v

example {X : Scheme.{u}} [IsNoetherian X] {ι : Type v} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) [∀ i, LocallyOfFiniteType (f i)]
    (hf : ∀ x : X, ∃ (i : ι) (y : Y i),
      f i y = x ∧ IsIso ((f i).residueFieldMap y)) :
    ∃ s : Finset ι, ∀ x : X, ∃ i ∈ s, ∃ y : Y i,
      f i y = x ∧ IsIso ((f i).residueFieldMap y) :=
  exists_finset_residueFieldLifting f hf

-- The selected arrows really form a Nisnevich family, with no new site definition.
example {X : Scheme.{u}} [IsNoetherian X] {ι : Type v} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) (hf : Presieve.ofArrows Y f ∈ precoverage X) :
    ∃ s : Finset ι,
      Presieve.ofArrows (fun i : s ↦ Y i) (fun i : s ↦ f i) ∈ precoverage X := by
  obtain ⟨s, hs⟩ := exists_finset_of_mem_precoverage f hf
  refine ⟨s, (ofArrows_mem_precoverage_iff _).mpr ⟨?_, ?_⟩⟩
  · exact fun i ↦ ((ofArrows_mem_precoverage_iff f).mp hf).1 i
  · intro x
    obtain ⟨i, hi, y, hy, hres⟩ := hs x
    exact ⟨⟨i, hi⟩, y, hy, hres⟩

-- The empty family over the empty scheme is accepted, not replaced by a nonempty one.
example {X : Scheme.{u}} [IsNoetherian X] [IsEmpty X]
    {Y : PEmpty.{v + 1} → Scheme.{u}} (f : ∀ i, Y i ⟶ X) :
    ∃ s : Finset PEmpty.{v + 1}, s = ∅ ∧
      ∀ x : X, ∃ i ∈ s, ∃ y : Y i,
        f i y = x ∧ IsIso ((f i).residueFieldMap y) := by
  let (i : PEmpty.{v + 1}) : LocallyOfFiniteType (f i) := i.elim
  obtain ⟨s, hs⟩ := exists_finset_residueFieldLifting f (fun x ↦ isEmptyElim x)
  exact ⟨s, Finset.eq_empty_of_isEmpty s, hs⟩

example {K : Type u} [Field K] {ι : Type v} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ Spec (.of K))
    (hf : Presieve.ofArrows Y f ∈ precoverage _) :
    ∃ s : Finset ι, ∀ x : Spec (.of K), ∃ i ∈ s, ∃ y : Y i,
      f i y = x ∧ IsIso ((f i).residueFieldMap y) :=
  exists_finset_of_mem_precoverage f hf

example {ι : Type v} {Y : ι → Scheme.{0}}
    (f : ∀ i, Y i ⟶ Spec (.of (ZMod 4)))
    (hf : Presieve.ofArrows Y f ∈ precoverage _) :
    ∃ s : Finset ι, ∀ x : Spec (.of (ZMod 4)), ∃ i ∈ s, ∃ y : Y i,
      f i y = x ∧ IsIso ((f i).residueFieldMap y) :=
  exists_finset_of_mem_precoverage f hf

example : (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 := by decide

set_option linter.hashCommand false in
#print axioms Motivic.Nisnevich.exists_finset_residueFieldLifting
set_option linter.hashCommand false in
#print axioms Motivic.Nisnevich.exists_finset_of_mem_precoverage
