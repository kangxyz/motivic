/-
Copyright (c) 2026 Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.QuasiAffine
public import Mathlib.RingTheory.Ideal.Operations

/-! # Affine neighborhoods of finite subsets of quasi-affine schemes -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
universe u

namespace PrimeSpectrum
/-- Prime avoidance chooses one principal neighborhood of an entire finite set. -/
theorem exists_basicOpen_of_finite_subset {R : Type u} [CommRing R]
    (U : Opens (PrimeSpectrum R)) (S : Set (PrimeSpectrum R)) (hS : S.Finite)
    (hSU : S ⊆ U) : ∃ r : R, S ⊆ basicOpen r ∧ basicOpen r ≤ U := by
  classical
  obtain ⟨I, hI⟩ := (isClosed_iff_zeroLocus_ideal ((U : Set (PrimeSpectrum R))ᶜ)).mp
    U.isOpen.isClosed_compl
  have hn : ¬ (I : Set R) ⊆ ⋃ p ∈ (PrimeSpectrum.asIdeal '' S), (p : Set R) := by
    intro h
    obtain ⟨p, ⟨x, hx, rfl⟩, hp⟩ :=
      (Ideal.subset_union_prime_finite (hS.image PrimeSpectrum.asIdeal)
        (f := id) 0 0 (by rintro p ⟨x, hx, rfl⟩ _ _; exact x.isPrime)).mp h
    have hxI : x ∈ zeroLocus (I : Set R) := hp
    rw [← hI] at hxI
    exact hxI (hSU hx)
  obtain ⟨r, hrI, hr⟩ := Set.not_subset.mp hn
  refine ⟨r, ?_, ?_⟩
  · intro x hx
    change r ∉ x.asIdeal
    intro hxr
    exact hr (Set.mem_iUnion₂.mpr ⟨x.asIdeal, ⟨x, hx, rfl⟩, hxr⟩)
  · intro x hx
    by_contra hxu
    have hxI : x ∈ zeroLocus (I : Set R) := by rw [← hI]; exact hxu
    exact hx (hxI hrI)
end PrimeSpectrum

namespace AlgebraicGeometry.Scheme
/-- Every finite subset of a quasi-affine scheme lies in one actual affine open. -/
theorem exists_isAffineOpen_of_finite {X : Scheme.{u}} [X.IsQuasiAffine]
    (S : Set X) (hS : S.Finite) : ∃ U : X.Opens, IsAffineOpen U ∧ S ⊆ U := by
  obtain ⟨r, hrS, hrU⟩ := PrimeSpectrum.exists_basicOpen_of_finite_subset
    X.toSpecΓ.opensRange (X.toSpecΓ '' S) (hS.image _) (Set.image_subset_range _ _)
  refine ⟨X.basicOpen r, ?_, ?_⟩
  · rw [← Hom.isAffineOpen_iff_of_isOpenImmersion X.toSpecΓ]
    rw [← X.toSpecΓ_preimage_basicOpen]
    have heq : X.toSpecΓ ''ᵁ (X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen r) =
        PrimeSpectrum.basicOpen r :=
      SetLike.coe_injective (Set.image_preimage_eq_of_subset hrU)
    rw [heq]
    exact IsAffineOpen.Spec_basicOpen r
  · intro x hx
    rw [← X.toSpecΓ_preimage_basicOpen]
    exact hrS (Set.mem_image_of_mem _ hx)
end AlgebraicGeometry.Scheme
