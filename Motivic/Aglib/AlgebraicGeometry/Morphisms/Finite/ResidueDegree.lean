/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.ResidueDegree
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Artinian

/-!
# Finiteness of finite-map residue degrees

The proof uses the actual scheme-theoretic fiber. A finite scheme over a field
is Artinian; consequently the residue-field point in the fiber is a closed
immersion. Composing it with the finite fiber projection proves that the
actual residue-field homomorphism is finite. Thus every residue degree used
for finite cycle pushforward is a positive finite extension degree.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- A finite scheme over an affine locally Artinian scheme is locally Artinian. -/
theorem isLocallyArtinian_of_finite_affine (f : X ⟶ Y) [IsFinite f]
    [IsAffine Y] [IsLocallyArtinian Y] : IsLocallyArtinian X := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let := f.appTop.hom.toAlgebra
  have : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := f.finite_appTop
  have : IsArtinianRing Γ(X, ⊤) := IsArtinianRing.of_finite Γ(Y, ⊤) Γ(X, ⊤)
  have : IsLocallyArtinian (Spec Γ(X, ⊤)) := Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  exact IsLocallyArtinian.of_isImmersion X.isoSpec.hom

/-- Fibers of a finite morphism are actually locally Artinian schemes. -/
theorem isLocallyArtinian_finiteFiber (f : X ⟶ Y) [IsFinite f] (y : Y) :
    IsLocallyArtinian (f.fiber y) := by
  have : IsFinite (f.fiberToSpecResidueField y) :=
    inferInstanceAs (IsFinite (CategoryTheory.Limits.pullback.snd _ _))
  have : IsLocallyArtinian (Spec (Y.residueField y)) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  exact isLocallyArtinian_of_finite_affine (f.fiberToSpecResidueField y)

/-- The actual residue-field map at every point of a finite morphism is finite. -/
theorem residueFieldMap_finite (f : X ⟶ Y) [IsFinite f] (x : X) :
    (f.residueFieldMap x).hom.Finite := by
  have := isLocallyArtinian_finiteFiber f (f x)
  have : IsClosedImmersion (f.asFiberHom x) :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [f.range_asFiberHom]; exact isClosed_singleton)
  have : IsFinite (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (IsFinite (CategoryTheory.Limits.pullback.snd _ _))
  have : IsFinite (Spec.map (f.residueFieldMap x)) := by
    rw [← f.asFiberHom_fiberToSpecResidueField x]
    infer_instance
  exact (IsFinite.SpecMap_iff _).mp this

/-- The finite pushforward coefficient never uses the zero-for-infinite convention. -/
theorem residueDegree_pos (f : X ⟶ Y) [IsFinite f] (x : X) : 0 < f.residueDegree x := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have : Module.Finite (Y.residueField (f x)) (X.residueField x) := residueFieldMap_finite f x
  exact Module.finrank_pos

end AlgebraicGeometry.Scheme.Hom
