/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Etale.ArtinianSections
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers of simultaneous Artinian étale sections

These consumers keep exact reduction at every maximal ideal and verify that the
section retracts the original scalar map. They include arbitrary finite products,
the nonreduced two-component base `ZMod 4 × ZMod 4`, and the zero ring with its
empty maximal spectrum. Neither the algebra nor the base is assumed local.
-/

@[expose] public noncomputable section

open _root_.Algebra.Etale.Artinian

namespace Motivic.MotivicTest.ArtinianEtaleSections

universe u v

example {R : Type u} {B : Type v} [CommRing R] [CommRing B] [IsArtinianRing R]
    [Algebra R B] [Algebra.Etale R B]
    (φ : ∀ q : MaximalSpectrum R, B →ₐ[R] R ⧸ q.asIdeal) :
    ∃ ψ : B →ₐ[R] R,
      ψ.toRingHom.comp (algebraMap R B) = RingHom.id R ∧
      ∀ (q : MaximalSpectrum R) (b : B), Ideal.Quotient.mk q.asIdeal (ψ b) = φ q b := by
  obtain ⟨ψ, hψ⟩ := exists_lift_of_etale φ
  refine ⟨ψ, ?_, fun q b ↦ DFunLike.congr_fun (hψ q) b⟩
  ext1 r
  exact ψ.commutes r

example {ι : Type u} [Finite ι] (R : ι → Type u) [∀ i, CommRing (R i)]
    [∀ i, IsArtinianRing (R i)] {B : Type v} [CommRing B]
    [Algebra (∀ i, R i) B] [Algebra.Etale (∀ i, R i) B]
    (φ : ∀ q : MaximalSpectrum (∀ i, R i), B →ₐ[∀ i, R i] (∀ i, R i) ⧸ q.asIdeal) :
    ∃ ψ : B →ₐ[∀ i, R i] (∀ i, R i), ∀ q : MaximalSpectrum (∀ i, R i),
      (Ideal.Quotient.mkₐ (∀ i, R i) q.asIdeal).comp ψ = φ q :=
  exists_lift_of_etale φ

/-- The concrete base has a nonzero square-zero element. -/
theorem nonreduced_witness :
    ∃ x : ZMod 4 × ZMod 4, x ≠ 0 ∧ x ^ 2 = 0 := by
  exact ⟨(2, 0), by decide, by decide⟩

/-- The concrete base is genuinely nonlocal. -/
theorem not_isLocalRing : ¬ IsLocalRing (ZMod 4 × ZMod 4) := by
  intro h
  have : Nontrivial (ZMod 4) := ⟨⟨0, 1, by decide⟩⟩
  have hu := IsLocalRing.isUnit_or_isUnit_of_add_one
    (show ((1, 0) : ZMod 4 × ZMod 4) + (0, 1) = 1 by decide)
  rcases hu with hu | hu
  · exact not_isUnit_zero (hu.map (RingHom.snd (ZMod 4) (ZMod 4)))
  · exact not_isUnit_zero (hu.map (RingHom.fst (ZMod 4) (ZMod 4)))

/-- All residue points lift over both components, including the nilpotent structure. -/
theorem nonreduced_twoComponent_section {B : Type v} [CommRing B]
    [Algebra (ZMod 4 × ZMod 4) B] [Algebra.Etale (ZMod 4 × ZMod 4) B]
    (φ : ∀ q : MaximalSpectrum (ZMod 4 × ZMod 4),
      B →ₐ[ZMod 4 × ZMod 4] (ZMod 4 × ZMod 4) ⧸ q.asIdeal) :
    ∃ ψ : B →ₐ[ZMod 4 × ZMod 4] (ZMod 4 × ZMod 4),
      ψ.toRingHom.comp (algebraMap (ZMod 4 × ZMod 4) B) = RingHom.id (ZMod 4 × ZMod 4) ∧
      ∀ q : MaximalSpectrum (ZMod 4 × ZMod 4),
        (Ideal.Quotient.mkₐ (ZMod 4 × ZMod 4) q.asIdeal).comp ψ = φ q := by
  have : IsArtinianRing (ZMod 4 × ZMod 4) := isArtinian_of_finite
  obtain ⟨ψ, hψ⟩ := exists_lift_of_etale φ
  refine ⟨ψ, ?_, hψ⟩
  ext1 r
  exact ψ.commutes r

/-- The formally smooth statement also applies to a polynomial algebra. -/
example {R : Type u} [CommRing R] [IsArtinianRing R]
    (φ : ∀ q : MaximalSpectrum R, MvPolynomial (Fin 1) R →ₐ[R] R ⧸ q.asIdeal) :
    ∃ ψ : MvPolynomial (Fin 1) R →ₐ[R] R, ∀ q : MaximalSpectrum R,
      (Ideal.Quotient.mkₐ R q.asIdeal).comp ψ = φ q :=
  exists_lift_of_formallySmooth φ

/-- No nontriviality or residue-point assumption is needed for the zero base ring. -/
theorem zeroRing_section {B : Type v} [CommRing B] [Algebra (ZMod 1) B]
    [Algebra.Etale (ZMod 1) B] : Nonempty (B →ₐ[ZMod 1] ZMod 1) := by
  have : IsArtinianRing (ZMod 1) := isArtinian_of_finite
  have hempty (q : MaximalSpectrum (ZMod 1)) : False :=
    q.isMaximal.ne_top (Subsingleton.elim _ _)
  obtain ⟨ψ, _⟩ := exists_lift_of_etale (R := ZMod 1) (B := B) (fun q ↦ (hempty q).elim)
  exact ⟨ψ⟩

set_option linter.hashCommand false in
#print axioms exists_lift_of_formallySmooth
set_option linter.hashCommand false in
#print axioms exists_lift_of_etale
set_option linter.hashCommand false in
#print axioms Motivic.MotivicTest.ArtinianEtaleSections.nonreduced_twoComponent_section
set_option linter.hashCommand false in
#print axioms Motivic.MotivicTest.ArtinianEtaleSections.zeroRing_section

end Motivic.MotivicTest.ArtinianEtaleSections
