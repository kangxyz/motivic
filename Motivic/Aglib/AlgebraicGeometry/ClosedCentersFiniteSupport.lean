/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Closed centers of a finite support

A locally quasi-finite source map has discrete fibers. Consequently, a point
above a closed source point is closed in the support. A locally finite-type
map from that support to a Jacobson target then has a closed target center.
In particular this applies to a finite support over a closed point, without
reducedness, flatness, or perfect-field hypotheses.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A point of a discrete fiber over a closed point is closed in the source. -/
theorem isClosed_singleton_of_isClosed_singleton_image
    {Z X : Scheme.{u}} (p : Z ⟶ X) [LocallyQuasiFinite p]
    (z : Z) (hx : IsClosed ({p z} : Set X)) : IsClosed ({z} : Set Z) := by
  let s : Set Z := p ⁻¹' {p z}
  have hs : IsClosed s := hx.preimage p.continuous
  let : DiscreteTopology s := (p.isDiscrete_preimage_singleton (p z)).to_subtype
  simpa only [Set.image_singleton] using
    hs.isClosedMap_subtype_val ({⟨z, rfl⟩} : Set s) (isClosed_discrete _)

/-- A locally finite-type map to a Jacobson scheme takes each point above a
closed point of a locally quasi-finite source map to a closed target point. -/
theorem isClosed_target_of_locallyQuasiFinite_source
    {Z X Y : Scheme.{u}} (p : Z ⟶ X) [LocallyQuasiFinite p]
    (t : Z ⟶ Y) [LocallyOfFiniteType t] [JacobsonSpace Y]
    (z : Z) (hx : IsClosed ({p z} : Set X)) : IsClosed ({t z} : Set Y) :=
  t.closePoints_subset_preimage_closedPoints
    (p.isClosed_singleton_of_isClosed_singleton_image z hx)

end AlgebraicGeometry.Scheme.Hom
