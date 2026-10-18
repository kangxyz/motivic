/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Affine boundary neighborhoods over the unchanged parameter

An affine boundary neighborhood remains affine after pullback to a specified
affine parameter scheme over a separated base. Affineness of the intervening
base is not required, and the parameter scheme is not replaced by an open.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurve

/-- The affine neighborhood maps affinely to a separated scheme over an affine
base; this avoids an unnecessary global affine-descent prerequisite. -/
theorem isAffineHom_boundaryNeighborhood {K S A : Scheme.{u}}
    [IsAffine K] [IsAffine A] (s : S ⟶ K) [IsSeparated s] (a : A ⟶ S) :
    IsAffineHom a := by
  have : IsAffineHom (a ≫ s) := inferInstance
  exact IsAffineHom.of_comp a s

/-- Base change preserves the whole affine neighborhood and the exact given
parameter scheme, without assuming that the intervening base is affine. -/
theorem isAffine_fixedParameter_boundaryNeighborhood {K S A T : Scheme.{u}}
    [IsAffine K] [IsAffine A] [IsAffine T]
    (s : S ⟶ K) [IsSeparated s] (a : A ⟶ S) (t : T ⟶ S) :
    IsAffine (pullback t a) := by
  have : IsAffineHom a := isAffineHom_boundaryNeighborhood s a
  infer_instance

end AlgebraicGeometry.Scheme.RelativeCurve
