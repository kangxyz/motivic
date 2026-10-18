/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.RetainedBoundaryNeighborhood
public import Motivic.Aglib.AlgebraicGeometry.ProperQuasiAffineZero

/-!
# Finite closed supports in an unchanged proper compactification

A closed subscheme supported inside a quasi-affine open of a proper scheme over
an affine base is finite over that original base. Applying this to the complement
of a boundary neighborhood supplies the opposite finite support without shrinking
any parameter scheme. This does not assert that the support is a Cartier divisor
or that a boundary-adapted ample line bundle has already been constructed.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurve

/-- Proper closed supports contained in the quasi-affine retained open are finite
on the unchanged affine base. The original closed scheme, including nilpotents,
is retained. No relative dimension, normality or flatness assumption is needed. -/
theorem isFinite_closed_support_in_quasiAffine_open
    {C S U D : Scheme.{u}} [IsAffine S] [U.IsQuasiAffine]
    (q : C ⟶ S) [IsProper q] (j : U ⟶ C) [IsOpenImmersion j]
    (d : D ⟶ C) [IsClosedImmersion d] (hd : Set.range d ⊆ Set.range j) :
    IsFinite (d ≫ q) := by
  let f := IsOpenImmersion.lift j d hd
  have hf : f ≫ j = d := IsOpenImmersion.lift_fac j d hd
  have : IsClosedImmersion (f ≫ j) := by rw [hf]; infer_instance
  have : IsClosedImmersion f := IsClosedImmersion.of_comp f j
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace q
  have : CompactSpace D := QuasiCompact.compactSpace_of_compactSpace d
  have : D.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion f
  exact Scheme.isFinite_of_isProper_of_isQuasiAffine (d ≫ q)

/-- If a boundary neighborhood contains the entire complement of the retained
quasi-affine curve, its own whole closed complement is finite over the same base.
This uses the existing native closed-complement scheme, not a replacement model. -/
theorem isFinite_complement_of_boundary_neighborhood
    {C S U : Scheme.{u}} [IsAffine S] [U.IsQuasiAffine]
    (q : C ⟶ S) [IsProper q] (j : U ⟶ C) [IsOpenImmersion j]
    (W : C.Opens) (hW : (Set.range j)ᶜ ⊆ (W : Set C)) :
    IsFinite (retainedBoundaryInclusion W ≫ q) := by
  apply isFinite_closed_support_in_quasiAffine_open q j
  rw [range_retainedBoundaryInclusion]
  intro x hx
  by_contra h
  exact hx (hW h)

end AlgebraicGeometry.Scheme.RelativeCurve
