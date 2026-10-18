/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Common base opens retaining complete marked fibers

For a finite morphism and a source open, remove the closed image of its whole
complement. The resulting base open has its entire inverse image in the given
open. A marked set survives precisely when all its lifts were retained.
Two finite morphisms admit the intersection of these actual base opens.
No rationality, reducedness, flatness or finiteness of the marked set is needed.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]

/-- Remove the image of the entire complement, not just unchosen marked lifts. -/
def finiteDescentOpen (O : X.Opens) : Y.Opens :=
  ⟨(f '' (O : Set X)ᶜ)ᶜ, (f.isClosedMap _ O.isOpen.isClosed_compl).isOpen_compl⟩

/-- The complete inverse image of the descended open lies in the source open. -/
theorem preimage_finiteDescentOpen_le (O : X.Opens) :
    f ⁻¹ᵁ f.finiteDescentOpen O ≤ O := by
  intro x hx
  by_contra hn
  exact hx ⟨x, hn, rfl⟩

/-- All marks survive if the source open contains every point over every mark. -/
theorem subset_finiteDescentOpen (O : X.Opens) (S : Set Y)
    (hS : f ⁻¹' S ⊆ (O : Set X)) :
    S ⊆ (f.finiteDescentOpen O : Set Y) := by
  rintro y hy ⟨x, hx, rfl⟩
  exact hx (hS hy)

/-- Full-fiber containment is exactly the condition for marks to survive. -/
theorem subset_finiteDescentOpen_iff (O : X.Opens) (S : Set Y) :
    S ⊆ (f.finiteDescentOpen O : Set Y) ↔ f ⁻¹' S ⊆ (O : Set X) := by
  constructor
  · intro h x hx
    exact f.preimage_finiteDescentOpen_le O (h hx)
  · exact f.subset_finiteDescentOpen O S

/-- The constructed open is the largest base open with the required full preimage. -/
theorem le_finiteDescentOpen_iff (O : X.Opens) (U : Y.Opens) :
    U ≤ f.finiteDescentOpen O ↔ f ⁻¹ᵁ U ≤ O :=
  f.subset_finiteDescentOpen_iff O (U : Set Y)

/-- Two finite extensions descend their source opens to one unchanged marked base. -/
theorem exists_common_marked_open {Z : Scheme.{u}} (g : Z ⟶ Y) [IsFinite g]
    (O : X.Opens) (V : Z.Opens) (S : Set Y)
    (hO : f ⁻¹' S ⊆ (O : Set X)) (hV : g ⁻¹' S ⊆ (V : Set Z)) :
    ∃ U : Y.Opens, S ⊆ (U : Set Y) ∧ f ⁻¹ᵁ U ≤ O ∧ g ⁻¹ᵁ U ≤ V := by
  refine ⟨f.finiteDescentOpen O ⊓ g.finiteDescentOpen V, ?_, ?_, ?_⟩
  · intro y hy
    exact ⟨f.subset_finiteDescentOpen O S hO hy,
      g.subset_finiteDescentOpen V S hV hy⟩
  · intro x hx
    exact f.preimage_finiteDescentOpen_le O hx.1
  · intro z hz
    exact g.preimage_finiteDescentOpen_le V hz.2

end AlgebraicGeometry.Scheme.Hom
