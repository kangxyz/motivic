/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.HenselianEtaleSections

/-!
# Consumers of henselian étale sections

These tests use arbitrary étale algebras, with no localness or module-finiteness
assumption on the algebra. They check pointwise residue compatibility, the
algebra-map retraction, and agreement with the residue equivalence for a field.
The final consumer derives henselianity for a local Artinian base, without any
reducedness assumption, from maximal-ideal completeness.
-/

open IsLocalRing Motivic.HenselianEtale

universe u v

example {R : Type u} [CommRing R] [HenselianLocalRing R]
    (P : StandardEtalePair R) (φ : P.Ring →ₐ[R] ResidueField R) :
    ∃ ψ : P.Ring →ₐ[R] R,
      (IsScalarTower.toAlgHom R R (ResidueField R)).comp ψ = φ :=
  exists_lift_of_standardEtalePair P φ

example {R : Type u} {B : Type v} [CommRing R] [CommRing B]
    [HenselianLocalRing R] [Algebra R B] [Algebra.IsStandardEtale R B]
    (φ : B →ₐ[R] ResidueField R) :
    ∃ ψ : B →ₐ[R] R, ∀ b, residue R (ψ b) = φ b := by
  obtain ⟨ψ, hψ⟩ := exists_lift_of_isStandardEtale φ
  exact ⟨ψ, fun b ↦ DFunLike.congr_fun hψ b⟩

example {R : Type u} {B : Type v} [CommRing R] [CommRing B]
    [HenselianLocalRing R] [Algebra R B] [Algebra.Etale R B]
    (φ : B →ₐ[R] ResidueField R) :
    ∃ ψ : B →ₐ[R] R,
      ψ.toRingHom.comp (algebraMap R B) = RingHom.id R ∧
      ∀ b, residue R (ψ b) = φ b := by
  obtain ⟨ψ, hψ⟩ := exists_lift_of_etale φ
  refine ⟨ψ, ?_, fun b ↦ DFunLike.congr_fun hψ b⟩
  ext r
  exact ψ.commutes r

example {K : Type u} {B : Type v} [Field K] [CommRing B]
    [Algebra K B] [Algebra.Etale K B] (φ : B →ₐ[K] ResidueField K) :
    let e : K ≃ₐ[K] ResidueField K :=
      AlgEquiv.ofBijective (Algebra.ofId K (ResidueField K))
        ⟨(residue K).injective, residue_surjective⟩
    ∃ ψ : B →ₐ[K] K, ψ = e.symm.toAlgHom.comp φ := by
  let e : K ≃ₐ[K] ResidueField K :=
    AlgEquiv.ofBijective (Algebra.ofId K (ResidueField K))
      ⟨(residue K).injective, residue_surjective⟩
  change ∃ ψ : B →ₐ[K] K, ψ = e.symm.toAlgHom.comp φ
  obtain ⟨ψ, hψ⟩ := exists_lift_of_etale φ
  refine ⟨ψ, ?_⟩
  ext b
  apply e.injective
  change e (ψ b) = e (e.symm (φ b))
  rw [e.apply_symm_apply]
  exact DFunLike.congr_fun hψ b

example {R : Type u} {B : Type v} [CommRing R] [CommRing B]
    [IsLocalRing R] [IsArtinianRing R] [Algebra R B] [Algebra.Etale R B]
    (φ : B →ₐ[R] ResidueField R) :
    ∃ ψ : B →ₐ[R] R,
      ψ.toRingHom.comp (algebraMap R B) = RingHom.id R ∧
      ∀ b, residue R (ψ b) = φ b := by
  obtain ⟨ψ, hψ⟩ := exists_lift_of_etale_of_artinian φ
  refine ⟨ψ, ?_, fun b ↦ DFunLike.congr_fun hψ b⟩
  ext r
  exact ψ.commutes r

set_option linter.hashCommand false in
#print axioms Motivic.HenselianEtale.exists_lift_of_standardEtalePair
set_option linter.hashCommand false in
#print axioms Motivic.HenselianEtale.exists_lift_of_isStandardEtale
set_option linter.hashCommand false in
#print axioms Motivic.HenselianEtale.exists_lift_of_etale
set_option linter.hashCommand false in
#print axioms Motivic.HenselianEtale.exists_lift_of_etale_of_artinian
