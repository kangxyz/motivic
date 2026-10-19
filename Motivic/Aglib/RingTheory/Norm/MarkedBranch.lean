/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PolynomialFiberNorm
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Unramified.Field

/-!
# Norms with one marked unramified branch

In a finite algebra over a field, a marked rational branch which is unramified
has local length one. If a function is one at every other residue branch, its
determinant norm is its value at the marked branch. The other local algebras
are not reduced: their complete lengths remain in the norm calculation.

The final statement specializes the actual determinant norm of a finite free
algebra over an arbitrary base to such a field-valued fiber. This is the
marked-fiber calculation used in the norm argument of MVW, Lemma 21.10. It does
not construct the norm of an arbitrary finite non-flat normal-scheme map or
assert its compatibility with etale base change or divisor pushforward.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra

attribute [local instance] RingHom.ker_isPrime

universe u v

variable {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B]
  [Module.Finite k B]

/-- A marked unramified branch of a finite field algebra has literal local
length one, without imposing reducedness on any other branch. -/
theorem local_length_eq_one_of_isUnramifiedAt (p : MaximalSpectrum B)
    [Algebra.IsUnramifiedAt k p.asIdeal] :
    Module.length (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal) = 1 := by
  have := Algebra.FormallyUnramified.finite_of_free k (Localization.AtPrime p.asIdeal)
  have := IsArtinianRing.of_finite k (Localization.AtPrime p.asIdeal)
  have := Algebra.FormallyUnramified.isReduced_of_field k (Localization.AtPrime p.asIdeal)
  let : Field (Localization.AtPrime p.asIdeal) :=
    (IsArtinianRing.isField_of_isReduced_of_isLocalRing _).toField
  exact Module.length_eq_one _ _

/-- The full length-weighted norm equals the value on its one marked rational
unramified branch when the values at all other residue branches are one. -/
theorem norm_eq_marked_residue_of_isUnramifiedAt (p : MaximalSpectrum B)
    [Algebra.IsUnramifiedAt k p.asIdeal] (e : (B ⧸ p.asIdeal) ≃ₐ[k] k) (b : B)
    (hone : ∀ q : MaximalSpectrum B, q ≠ p → Ideal.Quotient.mk q.asIdeal b = 1) :
    Algebra.norm k b = e (Ideal.Quotient.mk p.asIdeal b) := by
  classical
  let : Finite (MaximalSpectrum B) :=
    Module.finiteAlgebra_maximalSpectrum_finite k B
  let : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  calc
    Algebra.norm k b = ∏ q : MaximalSpectrum B,
        Algebra.norm k (Ideal.Quotient.mk q.asIdeal b) ^
          (Module.length (Localization.AtPrime q.asIdeal)
            (Localization.AtPrime q.asIdeal)).toNat :=
      norm_eq_prod_quotient_norm_pow_local_length b
    _ = Algebra.norm k (Ideal.Quotient.mk p.asIdeal b) ^
        (Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat := by
      apply Finset.prod_eq_single p
      · intro q _ hq
        simp only [hone q hq, map_one, one_pow]
      · simp
    _ = e (Ideal.Quotient.mk p.asIdeal b) := by
      rw [local_length_eq_one_of_isUnramifiedAt (k := k) p, ENat.toNat_one, pow_one]
      simpa only [Algebra.norm_self, MonoidHom.id_apply] using
        (Algebra.norm_eq_of_algEquiv e (Ideal.Quotient.mk p.asIdeal b)).symm

/-- A marked character supplies its own residue-field identification through
the literal quotient by its kernel. No replacement evaluation map is chosen. -/
theorem norm_eq_character_of_isUnramifiedAt (φ : B →ₐ[k] k)
    [Algebra.IsUnramifiedAt k (RingHom.ker φ)] (b : B)
    (hone : ∀ q : MaximalSpectrum B,
      q.asIdeal ≠ RingHom.ker φ → Ideal.Quotient.mk q.asIdeal b = 1) :
    Algebra.norm k b = φ b := by
  have hφ : Function.Surjective φ := fun a ↦ ⟨algebraMap k B a, by simp⟩
  let p : MaximalSpectrum B :=
    ⟨RingHom.ker φ, RingHom.ker_isMaximal_of_surjective φ hφ⟩
  have hp : Algebra.IsUnramifiedAt k p.asIdeal := inferInstance
  have h := norm_eq_marked_residue_of_isUnramifiedAt p
    (Ideal.quotientKerAlgEquivOfSurjective hφ) b (fun q hq ↦ hone q fun he ↦ hq (by
      exact MaximalSpectrum.ext he))
  simpa only [p, Ideal.quotientKerAlgEquivOfSurjective_mk] using h

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R k] [Algebra R S]
  [Module.Free R S] [Module.Finite R S]

/-- Specializing the original determinant norm to a field-valued fiber with
one marked unramified rational branch gives the original marked value.
Only the marked branch is unramified; all other fiber lengths are retained. -/
theorem map_norm_eq_marked_fiber
    (p : MaximalSpectrum (k ⊗[R] S)) [Algebra.IsUnramifiedAt k p.asIdeal]
    (e : ((k ⊗[R] S) ⧸ p.asIdeal) ≃ₐ[k] k) (s : S)
    (hone : ∀ q : MaximalSpectrum (k ⊗[R] S), q ≠ p →
      Ideal.Quotient.mk q.asIdeal ((1 : k) ⊗ₜ[R] s) = 1) :
    algebraMap R k (Algebra.norm R s) =
      e (Ideal.Quotient.mk p.asIdeal ((1 : k) ⊗ₜ[R] s)) := by
  rw [← Algebra.norm_one_tmul (A := k)]
  exact norm_eq_marked_residue_of_isUnramifiedAt p e _ hone

/-- The marked character version keeps the original evaluation map in the
specialized determinant-norm identity. The other residue branches may have
arbitrary nilpotent structure. -/
theorem map_norm_eq_fiber_character (φ : (k ⊗[R] S) →ₐ[k] k)
    [Algebra.IsUnramifiedAt k (RingHom.ker φ)] (s : S)
    (hone : ∀ q : MaximalSpectrum (k ⊗[R] S),
      q.asIdeal ≠ RingHom.ker φ →
        Ideal.Quotient.mk q.asIdeal ((1 : k) ⊗ₜ[R] s) = 1) :
    algebraMap R k (Algebra.norm R s) = φ ((1 : k) ⊗ₜ[R] s) := by
  rw [← Algebra.norm_one_tmul (A := k)]
  exact norm_eq_character_of_isUnramifiedAt φ _ hone

end Algebra
