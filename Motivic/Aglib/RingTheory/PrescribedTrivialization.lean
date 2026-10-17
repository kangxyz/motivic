/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Flat.LocallyFree
public import Mathlib.Algebra.Module.Projective

/-!
# Extending a prescribed rank-one quotient coordinate

A prescribed unit coordinate of a finite projective rank-one module after a
surjective scalar map extends to an actual principal localization. The defining
scalar restricts to one, and the localized coordinate retains the original
specified map on every original module element.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Module

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]

/-- Scalar extension across a surjective ring map is generated, as an additive
module, by the original elements with tensor coefficient one. -/
theorem tensor_mk_one_surjective (h : Function.Surjective (algebraMap R S)) :
    Function.Surjective (TensorProduct.mk R S M 1) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    obtain ⟨r, rfl⟩ := h s
    refine ⟨r • m, ?_⟩
    change (1 : S) ⊗ₜ[R] (r • m) = algebraMap R S r ⊗ₜ[R] m
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  | add x y hx hy =>
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := hy
    exact ⟨m + n, TensorProduct.tmul_add _ _ _⟩

/-- Lift the specified quotient coordinate to a global functional which is
an isomorphism on a principal neighborhood of the entire boundary. The global
functional is retained for functorial transport to actual sheaf morphisms. -/
theorem exists_prescribed_principal_coordinate_lift [Module.Finite R M]
    [Module.Projective R M]
    (hRank : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = 1)
    (h : Function.Surjective (algebraMap R S))
    (e : S ⊗[R] M ≃ₗ[S] S) :
    ∃ (f : M →ₗ[R] R),
      (∀ m : M, algebraMap R S (f m) = e (1 ⊗ₜ[R] m)) ∧
      ∃ (r : R), algebraMap R S r = 1 ∧
        ∃ (d : LocalizedModule.Away r M ≃ₗ[Localization.Away r] Localization.Away r),
          ∀ m : M,
            d (LocalizedModule.mkLinearMap (Submonoid.powers r) M m) =
              algebraMap R (Localization.Away r) (f m) := by
  let g : M →ₗ[R] S :=
    e.toLinearMap.restrictScalars R ∘ₗ TensorProduct.mk R S M 1
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (Algebra.linearMap R S) g h
  obtain ⟨m, hm⟩ := tensor_mk_one_surjective (M := M) h (e.symm 1)
  let r := f m
  have hr : algebraMap R S r = 1 := by
    have ht := LinearMap.congr_fun hf m
    change algebraMap R S (f m) = e (1 ⊗ₜ[R] m) at ht
    change (1 : S) ⊗ₜ[R] m = e.symm 1 at hm
    rw [hm, e.apply_symm_apply] at ht
    exact ht
  let f' : LocalizedModule.Away r M →ₗ[Localization.Away r] Localization.Away r :=
    LinearMap.extendScalarsOfIsLocalization (Submonoid.powers r) _ <|
      IsLocalizedModule.map (Submonoid.powers r)
        (LocalizedModule.mkLinearMap (Submonoid.powers r) M)
        (Algebra.linearMap R (Localization.Away r)) f
  have hmap (x : M) :
      f' (LocalizedModule.mkLinearMap (Submonoid.powers r) M x) =
        algebraMap R (Localization.Away r) (f x) :=
    IsLocalizedModule.map_apply _ _ _ _ _
  have hsurj : Function.Surjective f' :=
    LinearMap.range_eq_top.mp <| Ideal.eq_top_of_isUnit_mem _ ⟨_, hmap m⟩
      (IsLocalization.Away.algebraMap_isUnit r)
  have hbij : Function.Bijective f' :=
    Module.bijective_of_surjective_of_rankAtStalk_eq hsurj fun p _ ↦ by
      have : Nontrivial (Localization.Away r) :=
        nontrivial_of_ne 1 0 fun h10 ↦ p.one_notMem (by simpa only [h10] using p.zero_mem)
      rw [Module.rankAtStalk_isBaseChange
        (LocalizedModule.isBaseChange (Submonoid.powers r) M), hRank]
      simp [Module.rankAtStalk_eq_finrank_of_free]
  exact ⟨f, fun x ↦ LinearMap.congr_fun hf x, r, hr,
    LinearEquiv.ofBijective f' hbij, hmap⟩

/-- A specified quotient trivialization extends to an actual principal-local
unit coordinate with an exact scalar restriction equation. The neighborhood
scalar maps to one, so its basic open contains the entire closed subscheme. -/
theorem exists_prescribed_principal_coordinate [Module.Finite R M]
    [Module.Projective R M]
    (hRank : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = 1)
    (h : Function.Surjective (algebraMap R S))
    (e : S ⊗[R] M ≃ₗ[S] S) :
    ∃ (r : R) (hr : algebraMap R S r = 1)
      (d : LocalizedModule.Away r M ≃ₗ[Localization.Away r] Localization.Away r),
      ∀ m : M,
        IsLocalization.Away.lift r (hr ▸ isUnit_one)
            (d (LocalizedModule.mkLinearMap (Submonoid.powers r) M m)) =
          e (1 ⊗ₜ[R] m) := by
  obtain ⟨f, hf, r, hr, d, hd⟩ :=
    exists_prescribed_principal_coordinate_lift hRank h e
  refine ⟨r, hr, d, fun m ↦ ?_⟩
  rw [hd, IsLocalization.Away.lift_eq]
  exact hf m

/-- For a closed boundary defined by any ideal, the prescribed coordinate extends
on one principal open containing the entire scheme-theoretic boundary. The
condition `r - 1 ∈ I` retains the full ideal, not merely its radical. In
particular no reducedness, connectedness, or nonempty-boundary hypothesis is
required. -/
theorem exists_prescribed_principal_coordinate_quotient [Module.Finite R M]
    [Module.Projective R M]
    (hRank : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = 1)
    (I : Ideal R) (e : (R ⧸ I) ⊗[R] M ≃ₗ[R ⧸ I] R ⧸ I) :
    ∃ (r : R) (hr : algebraMap R (R ⧸ I) r = 1),
      r - 1 ∈ I ∧
      PrimeSpectrum.zeroLocus (I : Set R) ⊆ PrimeSpectrum.basicOpen r ∧
      ∃ (d : LocalizedModule.Away r M ≃ₗ[Localization.Away r] Localization.Away r),
        ∀ m : M,
          IsLocalization.Away.lift r (hr ▸ isUnit_one)
              (d (LocalizedModule.mkLinearMap (Submonoid.powers r) M m)) =
            e (1 ⊗ₜ[R] m) := by
  obtain ⟨r, hr, d, hd⟩ := exists_prescribed_principal_coordinate hRank
    (Ideal.Quotient.mk_surjective (I := I)) e
  have hI : r - 1 ∈ I := (Ideal.Quotient.mk_eq_one_iff_sub_mem (I := I) r).mp hr
  refine ⟨r, hr, hI, ?_, d, hd⟩
  intro p hp
  change r ∉ p.asIdeal
  intro hpr
  have hsub : r - 1 ∈ p.asIdeal := hp hI
  have hone : (1 : R) ∈ p.asIdeal := by
    simpa using p.asIdeal.sub_mem hpr hsub
  exact p.isPrime.one_notMem hone

end Module
