/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.LengthEuler.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.LocalRing.Length

/-!
# Finite Euler lengths under local restriction of scalars

For a local homomorphism with finite residue-field extension, restricting
scalars multiplies every module length by the actual residue degree. This
preserves finite-length support and multiplies the genuine signed Euler sum
by the same degree. The statement is about actual graded modules, with no
assumed formula for an intersection cycle or proper pushforward. It supplies
the local length calculation required by those later comparisons.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w

namespace HomologicalComplex.ModuleLengthEuler

variable (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [Module.Finite (ResidueField R) (ResidueField S)]

/-- The actual scalar-restriction functor satisfies the residue-degree length formula. -/
theorem length_restrictScalars (M : ModuleCat.{v} S) :
    Module.length R ((ModuleCat.restrictScalars (algebraMap R S)).obj M) =
      Module.length S M * (Module.finrank (ResidueField R) (ResidueField S) : ℕ∞) := by
  let := Module.compHom M (algebraMap R S)
  have : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  change Module.length R M = _
  rw [IsLocalRing.length_restrictScalars R S M, Module.length_eq_finrank]

/-- Finite module length remains finite after restriction with finite residue degree. -/
theorem length_restrictScalars_ne_top (M : ModuleCat.{v} S)
    (hM : Module.length S M ≠ ⊤) :
    Module.length R ((ModuleCat.restrictScalars (algebraMap R S)).obj M) ≠ ⊤ := by
  rw [length_restrictScalars]
  exact WithTop.mul_ne_top hM (ENat.natCast_ne_top _)

variable {ι : Type w} (X : ι → ModuleCat.{v} S)

/-- Genuine finite-length support is preserved; no infinite length is converted to an integer. -/
theorem FiniteLengthSupport.restrictScalars (hX : FiniteLengthSupport X) :
    FiniteLengthSupport (fun n => (ModuleCat.restrictScalars (algebraMap R S)).obj (X n)) where
  finite_length n := length_restrictScalars_ne_top R S (X n) (hX.finite_length n)
  finite_support := hX.finite_support.subset fun n hn => by
    contrapose! hn
    simp only [Function.mem_support, not_not] at hn ⊢
    rw [length_restrictScalars R S, hn, zero_mul]

/-- The actual finite integer length is multiplied by the actual residue degree. -/
theorem integerLength_restrictScalars (M : ModuleCat.{v} S)
    (hM : Module.length S M ≠ ⊤) :
    integerLength ((ModuleCat.restrictScalars (algebraMap R S)).obj M)
        (length_restrictScalars_ne_top R S M hM) =
      integerLength M hM * (Module.finrank (ResidueField R) (ResidueField S) : ℤ) := by
  simp only [integerLength, length_restrictScalars R S, ENat.toNat_mul,
    ENat.toNat_natCast, Nat.cast_mul]

/-- Every finite signed Euler sum transforms by the genuine residue-field degree. -/
theorem signedLengthSum_restrictScalars (sign : ι → ℤ) (hX : FiniteLengthSupport X) :
    signedLengthSum
        (fun n => (ModuleCat.restrictScalars (algebraMap R S)).obj (X n)) sign
        (hX.restrictScalars R S X) =
      signedLengthSum X sign hX * (Module.finrank (ResidueField R) (ResidueField S) : ℤ) := by
  unfold signedLengthSum
  rw [finsum_mul]
  apply finsum_congr
  intro n
  rw [integerLength_restrictScalars R S]
  exact (mul_assoc _ _ _).symm

end HomologicalComplex.ModuleLengthEuler
