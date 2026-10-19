/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Compactification.Retained.PrincipalRetainedBoundary
public import Lean

/-! # Full retained boundary and original prescribed scheme on one principal base -/
public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.RelativeCurve
universe u

example
    (R : Type u) [CommRing R] {C B Z : Scheme.{u}}
    (q : C ⟶ Spec (CommRingCat.of R)) [IsProper q] (b : B ⟶ C)
    [IsFinite (b ≫ q)] (U V : C.Opens) [IsAffine V.toScheme]
    (hboundary : (U : Set C)ᶜ ⊆ Set.range b) (s : Spec (CommRingCat.of R))
    (hwhole : ∀ x : C, q x = s → x ∈ U → x ∈ V)
    (z : Z ⟶ C) [IsFinite (z ≫ q)] (hzU : Set.range z ⊆ U) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
      IsFinite ((retainedBoundaryInclusion V ≫ q) ∣_ PrimeSpectrum.basicOpen r) ∧
      IsAffine (((V.ι ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme) ∧
      ∀ x : Z, (z ≫ q) x ∈ PrimeSpectrum.basicOpen r → z x ∈ V := by
  exact exists_principal_finite_retainedBoundary_preserving_scheme
    R q b U V hboundary s hwhole z hzU

open Lean in
run_cmd do
  for name in #[``exists_principal_finite_retainedBoundary_preserving_scheme,
      ``exists_finite_closed_retained_boundary] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Full boundary and unchanged prescribed scheme: standard axioms only."
