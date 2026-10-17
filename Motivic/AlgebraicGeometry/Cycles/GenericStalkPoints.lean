/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.GenericDominance
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Generic points of an actual scheme stalk

The canonical preimmersion from Spec of the actual stalk has exactly the
points specializing to the chosen point as its image. Its generalization
lifting and embedding identify its generic points with genuine global
component generic points whose closures contain that point. No Noetherian,
reducedness, irreducibility or dimension assumption is needed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic

variable {X Y : Scheme.{u}}

/-- An actual preimmersion reflects component genericity; injectivity, rather
than any unsupported quasi-finiteness of a localization, is used. -/
theorem mem_genericPoints_of_preimmersion_image (f : X ⟶ Y) [IsPreimmersion f]
    (x : X) (hx : f x ∈ genericPoints Y) : x ∈ genericPoints X := by
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro s hs hxs
  have h : hs.genericPoint ⤳ x := hs.isGenericPoint_genericPoint_closure.specializes
    (subset_closure (hxs (subset_closure (by simp))))
  have hy : f hs.genericPoint ⤳ f x := h.map f.continuous
  have hback : f x ⤳ f hs.genericPoint := specializes_iff_closure_subset.mpr
    (hx.2 isIrreducible_singleton.closure hy.closure_subset)
  have heq : hs.genericPoint = x := f.isEmbedding.injective (hy.antisymm hback).eq
  rw [← heq, hs.genericPoint_closure_eq]
  exact subset_closure

/-- The literal stalk-spectrum map lifts all generalizations. -/
theorem generalizingMap_fromSpecStalk (X : Scheme.{u}) (x : X) :
    GeneralizingMap (X.fromSpecStalk x) := by
  intro z y hy
  have hz : X.fromSpecStalk x z ⤳ x := by
    have h : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
    rwa [X.range_fromSpecStalk] at h
  have hr : y ∈ Set.range (X.fromSpecStalk x) := by
    rw [X.range_fromSpecStalk]
    exact hy.trans hz
  obtain ⟨w, hw⟩ := hr
  refine ⟨w, (X.fromSpecStalk x).isEmbedding.isInducing.specializes_iff.mp ?_, hw⟩
  simpa only [hw] using hy

/-- Actual stalk-spectrum generic points are exactly the global generic points
in the range of the canonical stalk map. -/
theorem fromSpecStalk_mem_genericPoints_iff (X : Scheme.{u}) (x : X)
    (p : Spec (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ∈ genericPoints X ↔
      p ∈ genericPoints (Spec (X.presheaf.stalk x)) :=
  ⟨mem_genericPoints_of_preimmersion_image _ p,
    mem_genericPoints_of_generalizing _ (generalizingMap_fromSpecStalk X x) p⟩

/-- The literal canonical map on component generics remembers specialization
at the chosen point of the original scheme. -/
noncomputable def stalkGenericPointMap (X : Scheme.{u}) (x : X)
    (p : genericPoints (Spec (X.presheaf.stalk x))) :
    {y : genericPoints X // y.1 ⤳ x} :=
  ⟨⟨X.fromSpecStalk x p.1, (fromSpecStalk_mem_genericPoints_iff X x p.1).mpr p.2⟩,
    by
      have h : X.fromSpecStalk x p.1 ∈ Set.range (X.fromSpecStalk x) := ⟨p.1, rfl⟩
      rwa [X.range_fromSpecStalk] at h⟩

/-- The actual stalk-spectrum generic-point map is bijective. -/
theorem stalkGenericPointMap_bijective (X : Scheme.{u}) (x : X) :
    Function.Bijective (stalkGenericPointMap X x) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply (X.fromSpecStalk x).isEmbedding.injective
    exact congrArg (fun y : {y : genericPoints X // y.1 ⤳ x} => y.1.1) hpq
  · intro y
    have h : y.1.1 ∈ Set.range (X.fromSpecStalk x) := by
      rw [X.range_fromSpecStalk]
      exact y.2
    obtain ⟨p, hp⟩ := h
    have hg : p ∈ genericPoints (Spec (X.presheaf.stalk x)) :=
      (fromSpecStalk_mem_genericPoints_iff X x p).mp (hp.symm ▸ y.1.2)
    refine ⟨⟨p, hg⟩, ?_⟩
    apply Subtype.ext
    exact Subtype.ext hp

/-- Generic points of the literal stalk spectrum correspond to actual global
component generic points whose closures contain the chosen point. -/
noncomputable def stalkGenericPointEquiv (X : Scheme.{u}) (x : X) :
    genericPoints (Spec (X.presheaf.stalk x)) ≃ {y : genericPoints X // y.1 ⤳ x} :=
  Equiv.ofBijective (stalkGenericPointMap X x) (stalkGenericPointMap_bijective X x)

@[simp]
theorem stalkGenericPointEquiv_apply_val (X : Scheme.{u}) (x : X)
    (p : genericPoints (Spec (X.presheaf.stalk x))) :
    (stalkGenericPointEquiv X x p).1.1 = X.fromSpecStalk x p.1 := rfl

end Motivic
