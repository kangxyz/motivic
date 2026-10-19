/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.MinimalComponentQuotient
public import Mathlib.RingTheory.Polynomial.Basic
public import Lean

/-! # Literal polynomial map on an unchanged nonreduced quotient and axiom audit -/
public noncomputable section
open AlgebraicGeometry _root_.MvPolynomial
universe u

example (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [IsNoetherianRing R] (n : ℕ) (f : Fin n → R) (I : Ideal R)
    (h : ∀ P ∈ (I ^ 2).minimalPrimes,
      IsFinite (Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk P).comp (aeval (R := k) f).toRingHom)))) :
    IsFinite (Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (I ^ 2)).comp (aeval (R := k) f).toRingHom))) := by
  exact isFinite_quotient_of_minimal_components (aeval (R := k) f).toRingHom (I ^ 2) h

open Lean in
run_cmd do
  for name in #[``Module.finite_quotient_of_minimal_components,
      ``RingHom.finite_quotient_of_minimal_components,
      ``isFinite_quotient_of_minimal_components] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original polynomial map and nonreduced quotient: standard axioms only."
