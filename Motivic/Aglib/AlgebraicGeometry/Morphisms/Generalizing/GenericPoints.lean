/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.FundamentalSupport
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Generic component dominance from generalization lifting

A generalizing scheme map sends every component generic point to a component
generic point. If the map is finite and its target irreducible, each source
component's reduced integral closure maps surjectively to the target. No
reducedness or integrality is assumed of the entire source scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- Generalization lifting sends actual component generic points to component generic points. -/
theorem mem_genericPoints_of_generalizing (f : X ⟶ Y) (hf : GeneralizingMap f)
    (x : X) (hx : x ∈ genericPoints X) : f x ∈ genericPoints Y := by
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro s hs hxs
  have hy : hs.genericPoint ⤳ f x :=
    hs.isGenericPoint_genericPoint_closure.specializes
      (subset_closure (hxs (subset_closure (by simp))))
  obtain ⟨x', hx'x, hfx'⟩ := hf hy
  have hxx' : x ⤳ x' := specializes_iff_closure_subset.mpr
    (hx.2 isIrreducible_singleton.closure hx'x.closure_subset)
  have heq : x' = x := (hx'x.antisymm hxx').eq
  subst x'
  rw [hfx', hs.genericPoint_closure_eq]
  exact subset_closure

/-- A finite generalizing map sends each source-component closure onto an
irreducible target. Nilpotents or other components of the source cause no change. -/
theorem image_closure_generic_eq_univ_of_finite_generalizing
    (f : X ⟶ Y) [IsFinite f] [IrreducibleSpace Y] (hf : GeneralizingMap f)
    (x : X) (hx : x ∈ genericPoints X) : f '' closure ({x} : Set X) = Set.univ := by
  have h := mem_genericPoints_of_generalizing f hf x hx
  have heq : closure ({f x} : Set Y) = Set.univ := by
    simpa only [genericPoints, Set.mem_ofPred_eq, irreducibleComponents_eq_singleton,
      Set.mem_singleton_iff] using h
  rw [← f.isClosedMap.closure_image_eq_of_continuous f.continuous, Set.image_singleton, heq]

/-- The actual reduced integral closed support of each generic source point
surjects under a finite generalizing map with irreducible target. -/
theorem surjective_pointClosure_of_finite_generalizing
    (f : X ⟶ Y) [IsFinite f] [IrreducibleSpace Y] (hf : GeneralizingMap f)
    (x : X) (hx : x ∈ genericPoints X) :
    Function.Surjective ((IntegralClosedSubscheme.pointClosure x).val.subschemeι ≫ f) := by
  apply Set.range_eq_univ.mp
  change Set.range (f ∘ (IntegralClosedSubscheme.pointClosure x).val.subschemeι) = Set.univ
  rw [Set.range_comp]
  rw [(IntegralClosedSubscheme.pointClosure x).val.range_subschemeι,
    IntegralClosedSubscheme.support_pointClosure]
  exact image_closure_generic_eq_univ_of_finite_generalizing f hf x hx

end AlgebraicGeometry.Scheme.Hom
