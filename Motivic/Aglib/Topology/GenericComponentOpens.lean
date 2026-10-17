/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

/-! # Disjoint actual opens around the finitely many component generic points -/
@[expose] public noncomputable section
open TopologicalSpace
universe u
namespace TopologicalSpace
variable (X : Type u) [TopologicalSpace X] [NoetherianSpace X] [T0Space X]

/-- Remove all the other irreducible components, retaining the full original
structure when this open is subsequently used on a scheme. -/
def genericComponentOpen (x : genericPoints X) : Opens X :=
  ⟨(⋃₀ (irreducibleComponents X \ {closure ({x.val} : Set X)}))ᶜ, by
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
      fun C hC => isClosed_of_mem_irreducibleComponents C hC.1⟩

omit [T0Space X] in
lemma mem_genericComponentOpen (x : genericPoints X) : x.val ∈ genericComponentOpen X x := by
  rintro ⟨C, hC, hxC⟩
  have hsub : closure ({x.val} : Set X) ⊆ C :=
    closure_minimal (Set.singleton_subset_iff.mpr hxC)
      (isClosed_of_mem_irreducibleComponents C hC.1)
  have heq : C = closure ({x.val} : Set X) :=
    Set.Subset.antisymm (x.property.2 hC.1.1 hsub) hsub
  exact hC.2 (Set.mem_singleton_iff.mpr heq)

lemma genericComponentOpen_pairwiseDisjoint :
    Pairwise fun x y : genericPoints X =>
      Disjoint (genericComponentOpen X x : Set X) (genericComponentOpen X y : Set X) := by
  intro x y hxy
  apply Set.disjoint_left.mpr
  intro z hzx hzy
  have hC := irreducibleComponent_mem_irreducibleComponents z
  have hx : irreducibleComponent z = closure ({x.val} : Set X) := by
    by_contra hn
    exact hzx ⟨_, ⟨hC, by simpa using hn⟩, mem_irreducibleComponent⟩
  have hy : irreducibleComponent z = closure ({y.val} : Set X) := by
    by_contra hn
    exact hzy ⟨_, ⟨hC, by simpa using hn⟩, mem_irreducibleComponent⟩
  apply hxy
  apply genericPoints.component_injective
  exact Subtype.ext (hx.symm.trans hy)

end TopologicalSpace
