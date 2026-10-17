/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.AffineLineEtaleCompactification

/-! Original affine-line étale cover, actual compactification, finite full infinity. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry
open Scheme.AffineLineEtaleCompactification
universe u

example (k : Type u) [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p] :
    IsOpenImmersion (inclusion k p) ∧ IsFinite (toProjectiveLine k p) ∧
      IsProper (projection k p) ∧ IsFinite (infinityInclusion k p ≫ projection k p) ∧
      inclusion k p ≫ projection k p =
        p ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inclusion_projection k p⟩

#print axioms AlgebraicGeometry.Scheme.AffineLineEtaleCompactification.finite_infinity
#print axioms AlgebraicGeometry.Scheme.AffineLineEtaleCompactification.inclusion_projection
