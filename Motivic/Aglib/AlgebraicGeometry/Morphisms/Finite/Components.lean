/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Generalizing.GenericPoints
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Images of components under finite generalizing morphisms

A finite generalizing morphism sends each irreducible component onto an
irreducible component, even when both schemes are disconnected or nonreduced.
The image is the literal image of the closure of its generic point. Flatness
supplies generalization lifting; finiteness alone does not.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- Finiteness identifies the image of a component closure with the closure
of the original generic point's image. -/
theorem image_closure_singleton_of_isFinite (f : X ⟶ Y) [IsFinite f] (x : X) :
    f '' closure ({x} : Set X) = closure ({f x} : Set Y) := by
  rw [← f.isClosedMap.closure_image_eq_of_continuous f.continuous, Set.image_singleton]

/-- Finite generalization lifting preserves the actual irreducible-component
image, without requiring the target to be irreducible. -/
theorem image_closure_mem_irreducibleComponents_of_finite_generalizing
    (f : X ⟶ Y) [IsFinite f] (hf : GeneralizingMap f)
    (x : X) (hx : x ∈ genericPoints X) :
    f '' closure ({x} : Set X) ∈ irreducibleComponents Y := by
  rw [image_closure_singleton_of_isFinite]
  exact mem_genericPoints_of_generalizing f hf x hx

/-- Every generic component of a finite flat scheme maps onto an actual
component of its base. Empty schemes and nilpotents are allowed. -/
theorem image_closure_mem_irreducibleComponents_of_finite_flat
    (f : X ⟶ Y) [IsFinite f] [Flat f] (x : X) (hx : x ∈ genericPoints X) :
    f '' closure ({x} : Set X) ∈ irreducibleComponents Y :=
  image_closure_mem_irreducibleComponents_of_finite_generalizing f
    (Flat.generalizingMap f) x hx

end AlgebraicGeometry.Scheme.Hom
