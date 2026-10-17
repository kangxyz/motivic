/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Etale.Basic

/-!
# Simultaneous residue-compatible sections over Artinian rings

A point in every residue field of a commutative Artinian ring assembles to a
point over its reduced quotient. Formal smoothness lifts this point across the
nilpotent nilradical to the complete Artinian base, with exactly the prescribed
reduction at every maximal ideal. In particular this gives a section of any
étale algebra having prescribed rational points on all components.

The base need not be reduced, nontrivial, or local, and the algebra need not be
local or module-finite. The empty spectrum of the zero ring is allowed.
-/

@[expose] public noncomputable section

namespace Motivic.ArtinianEtale

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] [IsArtinianRing R]

/-- Prescribed residue-field points of a formally smooth algebra over an Artinian
ring lift simultaneously to a section over the entire, possibly nonreduced base. -/
theorem exists_lift_of_formallySmooth [Algebra.FormallySmooth R B]
    (φ : ∀ q : MaximalSpectrum R, B →ₐ[R] R ⧸ q.asIdeal) :
    ∃ ψ : B →ₐ[R] R, ∀ q : MaximalSpectrum R,
      (Ideal.Quotient.mkₐ R q.asIdeal).comp ψ = φ q := by
  let e := IsArtinianRing.quotNilradicalEquivPi R
  obtain ⟨ψ, hψ⟩ := Algebra.FormallySmooth.exists_lift (nilradical R)
    IsArtinianRing.isNilpotent_nilradical (e.symm.toAlgHom.comp (AlgHom.pi φ))
  refine ⟨ψ, fun q ↦ ?_⟩
  ext b
  have h := congrArg (fun x ↦ e x q) (DFunLike.congr_fun hψ b)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] at h
  change e (algebraMap R (R ⧸ nilradical R) (ψ b)) q = _ at h
  rw [e.commutes] at h
  exact h

/-- An étale algebra with a prescribed rational point at every maximal ideal of
an Artinian base admits a section with exactly those reductions. -/
theorem exists_lift_of_etale [Algebra.Etale R B]
    (φ : ∀ q : MaximalSpectrum R, B →ₐ[R] R ⧸ q.asIdeal) :
    ∃ ψ : B →ₐ[R] R, ∀ q : MaximalSpectrum R,
      (Ideal.Quotient.mkₐ R q.asIdeal).comp ψ = φ q :=
  exists_lift_of_formallySmooth φ

end Motivic.ArtinianEtale
