/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Charts
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting

/-! # Coefficient change of the actual projective transition units -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MvPolynomial HomogeneousLocalization TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable {R S : Type u} [CommRing R] [CommRing S]

/-- A subopen of a pulled-back chart is a subopen of the same coordinate chart. -/
theorem le_coordinateOpen_of_le_preimage (f : R →+* S) (ι : Type u) (i : ι)
    {V : (ProjectiveSpace R ι).Opens} {W : (ProjectiveSpace S ι).Opens}
    (h : W ≤ map f ι ⁻¹ᵁ V) (hi : V ≤ coordinateOpen R ι i) :
    W ≤ coordinateOpen S ι i := by
  rw [← map_preimage_coordinateOpen f ι i]
  exact h.trans ((Opens.map (map f ι).base).map (homOfLE hi)).le

/-- The native structure-sheaf map preserves transition units on all common subopens. -/
theorem coordinateTransitionOn_map_appLE (f : R →+* S) (ι : Type u) (i j : ι)
    {V : (ProjectiveSpace R ι).Opens} {W : (ProjectiveSpace S ι).Opens}
    (h : W ≤ map f ι ⁻¹ᵁ V)
    (hi : V ≤ coordinateOpen R ι i) (hj : V ≤ coordinateOpen R ι j) :
    Units.map ((map f ι).appLE V W h).hom.toMonoidHom
        (coordinateTransitionOn R ι i j hi hj) =
      coordinateTransitionOn S ι i j
        (le_coordinateOpen_of_le_preimage f ι i h hi)
        (le_coordinateOpen_of_le_preimage f ι j h hj) := by
  apply Units.ext
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  change (localRingHom (gradedMap f) _ x.val.asHomogeneousIdeal.toIdeal rfl
    (HomogeneousLocalization.mapId _ _
      (coordinateOverlapRatio R ι i j i))).val =
    (HomogeneousLocalization.mapId _ _ (coordinateOverlapRatio S ι i j i)).val
  simp [coordinateOverlapRatio, HomogeneousLocalization.mapId,
    HomogeneousLocalization.map, Away.mk, HomogeneousLocalization.localRingHom]

/-- Exact inverse-image specialization, using the original scheme morphism's `app`. -/
theorem coordinateTransitionOn_map_app (f : R →+* S) (ι : Type u) (i j : ι)
    {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) (hj : V ≤ coordinateOpen R ι j) :
    Units.map ((map f ι).app V).hom.toMonoidHom
        (coordinateTransitionOn R ι i j hi hj) =
      coordinateTransitionOn S ι i j
        (le_coordinateOpen_of_le_preimage f ι i le_rfl hi)
        (le_coordinateOpen_of_le_preimage f ι j le_rfl hj) := by
  simpa only [Scheme.Hom.appLE_eq_app] using
    coordinateTransitionOn_map_appLE f ι i j le_rfl hi hj

/-- Coefficient change preserves every integral twisting cocycle on the native sheaf. -/
theorem coordinateTransitionOn_zpow_map_app (f : R →+* S) (ι : Type u) (i j : ι)
    {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) (hj : V ≤ coordinateOpen R ι j) (n : ℤ) :
    Units.map ((map f ι).app V).hom.toMonoidHom
        (coordinateTransitionOn R ι i j hi hj ^ n) =
      coordinateTransitionOn S ι i j
        (le_coordinateOpen_of_le_preimage f ι i le_rfl hi)
        (le_coordinateOpen_of_le_preimage f ι j le_rfl hj) ^ n := by
  rw [map_zpow, coordinateTransitionOn_map_app]

end AlgebraicGeometry.ProjectiveSpace
