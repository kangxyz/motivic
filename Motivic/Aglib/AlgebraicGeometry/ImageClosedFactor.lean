/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Descending a closed-support factorization to the actual image

If the composite `D ⟶ V ⟶ Z` factors through a closed immersion `C ⟶ Z`,
then the scheme-theoretic image of `D ⟶ V` has a canonical map to `C`.
Both triangles commute with the original maps. The proof compares the actual
ideal-sheaf kernels, rather than only their topological supports; neither
reducedness nor finiteness is needed.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {D V Z C : Scheme.{u}} (m : D ⟶ V) (t : V ⟶ Z)

/-- Passing to the actual scheme-theoretic image does not change the kernel
after an arbitrary target morphism. -/
theorem imageι_comp_ker_eq : (m.imageι ≫ t).ker = (m ≫ t).ker := by
  simp only [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι]

variable (j : C ⟶ Z) [IsClosedImmersion j] (a : D ⟶ C) (h : a ≫ j = m ≫ t)

/-- The canonical map from the actual image to the prescribed closed support. -/
def imageToClosedFactor : m.image ⟶ C :=
  IsClosedImmersion.lift j (m.imageι ≫ t) (by
    rw [m.imageι_comp_ker_eq, ← h]
    exact a.le_ker_comp j)

/-- The descended support map retains the literal postcomposition in the ambient scheme. -/
@[reassoc (attr := simp)]
theorem imageToClosedFactor_comp :
    m.imageToClosedFactor t j a h ≫ j = m.imageι ≫ t :=
  IsClosedImmersion.lift_fac _ _ _

/-- The original support map factors through the actual image with no reduction. -/
@[reassoc (attr := simp)]
theorem toImage_imageToClosedFactor : m.toImage ≫ m.imageToClosedFactor t j a h = a := by
  apply (cancel_mono j).mp
  rw [Category.assoc, m.imageToClosedFactor_comp, ← Category.assoc, m.toImage_imageι]
  exact h.symm

/-- The descended map is uniquely specified by its actual ambient factorization. -/
theorem imageToClosedFactor_unique (r : m.image ⟶ C) (hr : r ≫ j = m.imageι ≫ t) :
    r = m.imageToClosedFactor t j a h := by
  apply (cancel_mono j).mp
  rw [hr, m.imageToClosedFactor_comp]

end AlgebraicGeometry.Scheme.Hom
