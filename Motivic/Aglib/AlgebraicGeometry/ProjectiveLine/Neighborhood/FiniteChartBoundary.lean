/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
/-! # Whole finite boundaries contained in an affine projective chart

A closed boundary in a proper scheme which misses the complementary hyperplane
is finite over an affine base. The original closed scheme is retained, with
no reducedness or flatness assumption.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- Properness plus an actual affine-chart factorization proves finiteness. -/
theorem isFinite_closed_boundary_in_affine_chart {C S B : Scheme.{u}}
    (p : C ⟶ S) [IsProper p] [IsAffine S]
    (i : B ⟶ C) [IsClosedImmersion i]
    (U : C.Opens) (hU : IsAffineOpen U) (h : Set.range i ⊆ U) :
    IsFinite (i ≫ p) := by
  let g := IsOpenImmersion.lift U.ι i (by simpa using h)
  have hp := IsOpenImmersion.isPullback_lift_id i U.ι (by simpa using h)
  have : IsClosedImmersion g := by
    change IsClosedImmersion (IsOpenImmersion.lift U.ι i _)
    rw [← hp.isoPullback_hom_fst]
    infer_instance
  have : IsAffine U := hU
  have : IsAffine B := isAffine_of_isAffineHom g
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProjectiveSpace
variable (R : Type u) [CommRing R] (ι : Type u) [Finite ι]

/-- In particular a whole closed boundary lying in any standard projective chart is finite. -/
theorem isFinite_boundary_in_coordinateOpen {B : Scheme.{u}}
    (i : B ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    (j : ι) (h : Set.range i ⊆ coordinateOpen R ι j) :
    IsFinite (i ≫ toSpec R ι) :=
  Scheme.isFinite_closed_boundary_in_affine_chart (toSpec R ι) i _
    (isAffineOpen_coordinateOpen R ι j) h
end AlgebraicGeometry.ProjectiveSpace
