/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.GenericDominance
public import Motivic.AlgebraicGeometry.Cycles.GenericStalkSupport
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Actual fibers above generic points

A locally quasi-finite scheme map reflects generic points: a point mapping to
an actual generic point has no strict generization, because its fiber is
discrete. This gives a literal reindexing of that fiber by source generic
points. No dimension, purity, integrality or reducedness assumption is used.
The converse direction needs a genuine generalizing-map hypothesis; finite
maps alone need not send every source generic point to a target generic point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]

/-- A generization above a generic target point must equal the original point. -/
theorem specializes_eq_of_image_generic {x' x : X} (hx : f x ∈ genericPoints Y)
    (h : x' ⤳ x) : x' = x := by
  have hy : f x' ⤳ f x := h.map f.continuous
  have hback : f x ⤳ f x' := specializes_iff_closure_subset.mpr
    (hx.2 isIrreducible_singleton.closure hy.closure_subset)
  have heq : f x' = f x := (hy.antisymm hback).eq
  exact (f.isDiscrete_preimage_singleton (f x)).eq_of_specializes h heq rfl

/-- Locally quasi-finite morphisms reflect actual component generic points. -/
theorem mem_genericPoints_of_image_generic (x : X) (hx : f x ∈ genericPoints Y) :
    x ∈ genericPoints X := by
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro s hs hxs
  have h : hs.genericPoint ⤳ x := hs.isGenericPoint_genericPoint_closure.specializes
    (subset_closure (hxs (subset_closure (by simp))))
  have heq := specializes_eq_of_image_generic f hx h
  rw [← heq, hs.genericPoint_closure_eq]
  exact subset_closure

/-- With genuine generalization lifting, the generic-point criterion is bidirectional. -/
theorem image_mem_genericPoints_iff_of_generalizing (hf : GeneralizingMap f) (x : X) :
    f x ∈ genericPoints Y ↔ x ∈ genericPoints X :=
  ⟨mem_genericPoints_of_image_generic f x, mem_genericPoints_of_generalizing f hf x⟩

/-- The actual point fiber above a generic target point consists exactly of
source generic points; this is an equivalence, not a product-of-stalks claim. -/
def genericFiberEquiv (y : genericPoints Y) :
    {x : X // f x = y.1} ≃ {x : genericPoints X // f x.1 = y.1} where
  toFun x := ⟨⟨x.1, mem_genericPoints_of_image_generic f x.1 (by simpa only [x.2] using y.2)⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem genericFiberEquiv_apply_val (y : genericPoints Y) (x : {x : X // f x = y.1}) :
    ((genericFiberEquiv f y x).1 : X) = x.1 := rfl

@[simp]
theorem genericFiberEquiv_symm_apply_val (y : genericPoints Y)
    (x : {x : genericPoints X // f x.1 = y.1}) :
    ((genericFiberEquiv f y).symm x : X) = x.1.1 := rfl

/-- An actual source stalk over a generic target point is Artinian when the
source is locally Noetherian. The source may be nonreduced or disconnected. -/
theorem isArtinianRing_stalk_of_image_generic [IsLocallyNoetherian X]
    (x : X) (hx : f x ∈ genericPoints Y) : IsArtinianRing (X.presheaf.stalk x) :=
  isArtinianRing_stalk_of_mem_genericPoints x (mem_genericPoints_of_image_generic f x hx)

/-- A surjective ambient stalk map cuts out an Artinian actual source stalk
above a generic target point, without claiming that the ambient ring is Artinian. -/
theorem stalk_quotient_ker_isArtinian_of_image_generic {T : Scheme.{u}}
    (i : X ⟶ T) [SurjectiveOnStalks i] [IsLocallyNoetherian X]
    (x : X) (hx : f x ∈ genericPoints Y) :
    IsArtinianRing ((T.presheaf.stalk (i x)) ⧸ RingHom.ker (i.stalkMap x).hom) :=
  stalk_quotient_ker_isArtinian i x (mem_genericPoints_of_image_generic f x hx)

end Motivic
