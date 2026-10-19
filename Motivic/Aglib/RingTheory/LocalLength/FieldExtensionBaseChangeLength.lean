/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteLength.FiniteAlgebraLength
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.Data.ENat.BigOperators

/-!
# Residue-degree balance for a field extension over an Artinian local algebra

For a finite field extension `K → L` and an Artinian local `K`-algebra `R`,
the actual tensor algebra `R ⊗[K] L` is finite free of rank `[L : K]` over `R`.
Its all-point finite-algebra length formula therefore gives the sum of its
actual local lengths times their actual residue degrees. The sum equals
`[L : K] * length R R`, including every branch and all nilpotent multiplicities.

The scalar square is the literal tensor square, and residue comparisons require
compatibility with the original `R`-action. No separability, reducedness,
single-point fiber, geometric generic-point bijection or coefficient equality
is assumed. Attaching this algebra to original exterior support stalks requires
additional geometric quotient and localization identifications.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w w'

namespace Module

variable (K : Type u) (L : Type v) (R : Type w)
  [Field K] [Field L] [Algebra K L] [Module.Finite K L]
  [CommRing R] [Algebra K R]

omit [Module.Finite K L] in
/-- Both actual tensor inclusions agree on the original field. -/
theorem fieldExtensionBaseChange_square :
    (Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap K R) :
        K →+* R ⊗[K] L) =
      Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap K L) :=
  Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap

omit [Module.Finite K L] in
/-- Localization retains the actual tensor scalar square on the original field. -/
theorem fieldExtensionBaseChange_localSquare (q : MaximalSpectrum (R ⊗[K] L)) :
    (algebraMap (R ⊗[K] L) (Localization.AtPrime q.asIdeal)).comp
        (Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap K R)) =
      (algebraMap (R ⊗[K] L) (Localization.AtPrime q.asIdeal)).comp
        (Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap K L)) :=
  congrArg (RingHom.comp (algebraMap (R ⊗[K] L) (Localization.AtPrime q.asIdeal)))
    (fieldExtensionBaseChange_square K L R)

omit [Module.Finite K L] in
/-- Every actual maximal quotient retains the same original-field scalar square. -/
theorem fieldExtensionBaseChange_quotientSquare (q : MaximalSpectrum (R ⊗[K] L)) :
    (Ideal.Quotient.mk q.asIdeal).comp
        (Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap K R)) =
      (Ideal.Quotient.mk q.asIdeal).comp
        (Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap K L)) :=
  congrArg (RingHom.comp (Ideal.Quotient.mk q.asIdeal))
    (fieldExtensionBaseChange_square K L R)

/-- The actual finite free tensor algebra retains the length of the whole base ring. -/
theorem fieldExtensionBaseChange_restrictedLength [Nontrivial R] :
    Module.length R (R ⊗[K] L) =
      (Module.finrank K L : ℕ∞) * Module.length R R := by
  rw [Module.length_of_free_of_finite, Module.finrank_baseChange]

variable [IsLocalRing R]

attribute [local instance] Ideal.Quotient.field

/-- The actual maximal quotient's scalar map from `R` determines its residue action.
An abstract field isomorphism without this square is insufficient. -/
theorem fieldExtensionBaseChange_residueSquare
    (q : MaximalSpectrum (R ⊗[K] L))
    {E : Type w'} [Field E] [Algebra R E]
    [Algebra (IsLocalRing.ResidueField R) E]
    [IsScalarTower R (IsLocalRing.ResidueField R) E]
    (e : ((R ⊗[K] L) ⧸ q.asIdeal) ≃+* E)
    (h : e.toRingHom.comp (algebraMap R ((R ⊗[K] L) ⧸ q.asIdeal)) = algebraMap R E) :
    e.toRingHom.comp
        (algebraMap (IsLocalRing.ResidueField R) ((R ⊗[K] L) ⧸ q.asIdeal)) =
      algebraMap (IsLocalRing.ResidueField R) E := by
  apply RingHom.ext
  intro x
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  change e (algebraMap (IsLocalRing.ResidueField R) ((R ⊗[K] L) ⧸ q.asIdeal)
      (algebraMap R (IsLocalRing.ResidueField R) r)) =
    algebraMap (IsLocalRing.ResidueField R) E (algebraMap R (IsLocalRing.ResidueField R) r)
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  exact RingHom.congr_fun h r

/-- A comparison respecting the actual base map preserves the residue degree. -/
theorem fieldExtensionBaseChange_residueDegree_eq_of_square
    (q : MaximalSpectrum (R ⊗[K] L))
    {E : Type w'} [Field E] [Algebra R E]
    [Algebra (IsLocalRing.ResidueField R) E]
    [IsScalarTower R (IsLocalRing.ResidueField R) E]
    (e : ((R ⊗[K] L) ⧸ q.asIdeal) ≃+* E)
    (h : e.toRingHom.comp (algebraMap R ((R ⊗[K] L) ⧸ q.asIdeal)) = algebraMap R E) :
    finiteAlgebraResidueDegree R (R ⊗[K] L) q =
      Module.finrank (IsLocalRing.ResidueField R) E := by
  exact Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _) e
    (by simpa using (fieldExtensionBaseChange_residueSquare K L R q e h).symm)

variable [IsArtinianRing R]

omit [IsLocalRing R] in
/-- The entire tensor algebra is Artinian by finite generation over the actual base. -/
theorem fieldExtensionBaseChange_artinian : IsArtinianRing (R ⊗[K] L) :=
  IsArtinianRing.of_finite R (R ⊗[K] L)

omit [IsLocalRing R] in
/-- All actual branch lengths are finite before converting them to integers. -/
theorem fieldExtensionBaseChange_localLength_ne_top
    (q : MaximalSpectrum (R ⊗[K] L)) :
    Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) ≠ ⊤ := by
  have := fieldExtensionBaseChange_artinian K L R
  exact Module.length_ne_top

/-- All closed branches contribute their true lengths and residue degrees;
their total is the original field degree times the unreduced base length. -/
theorem fieldExtensionBaseChange_sum_length_mul_residueDegree
    [Fintype (MaximalSpectrum (R ⊗[K] L))] :
    (∑ q : MaximalSpectrum (R ⊗[K] L),
      Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) *
        (finiteAlgebraResidueDegree R (R ⊗[K] L) q : ℕ∞)) =
      (Module.finrank K L : ℕ∞) * Module.length R R := by
  have := fieldExtensionBaseChange_artinian K L R
  have h := finiteAlgebra_length_eq_sum (M := R ⊗[K] L) R (R ⊗[K] L)
    Module.length_ne_top
  have hlocal (q : MaximalSpectrum (R ⊗[K] L)) :
      Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal ⊗[R ⊗[K] L] (R ⊗[K] L)) =
        Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) :=
    (TensorProduct.AlgebraTensorModule.rid (R ⊗[K] L)
      (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).length_eq
  simpa only [hlocal] using h.symm.trans (fieldExtensionBaseChange_restrictedLength K L R)

/-- The all-branch sum uses finiteness derived from the actual finite algebra. -/
def fieldExtensionBaseChangeLengthSum : ℕ∞ :=
  let := finiteAlgebra_maximalSpectrum_finite R (R ⊗[K] L)
  let := Fintype.ofFinite (MaximalSpectrum (R ⊗[K] L))
  ∑ q : MaximalSpectrum (R ⊗[K] L),
    Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) *
      (finiteAlgebraResidueDegree R (R ⊗[K] L) q : ℕ∞)

/-- Canonical degree-length balance without a supplied point enumeration. -/
theorem fieldExtensionBaseChangeLengthSum_eq :
    fieldExtensionBaseChangeLengthSum K L R =
      (Module.finrank K L : ℕ∞) * Module.length R R := by
  let := finiteAlgebra_maximalSpectrum_finite R (R ⊗[K] L)
  let := Fintype.ofFinite (MaximalSpectrum (R ⊗[K] L))
  exact fieldExtensionBaseChange_sum_length_mul_residueDegree K L R

/-- Integer conversion follows the proved finiteness of every actual branch;
the original field degree and the actual base multiplicity both remain. -/
theorem fieldExtensionBaseChange_sum_integerLength_mul_residueDegree
    [Fintype (MaximalSpectrum (R ⊗[K] L))] :
    (∑ q : MaximalSpectrum (R ⊗[K] L),
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℤ) *
          (finiteAlgebraResidueDegree R (R ⊗[K] L) q : ℤ)) =
      (Module.finrank K L : ℤ) * ((Module.length R R).toNat : ℤ) := by
  have h := congrArg ENat.toNat
    (fieldExtensionBaseChange_sum_length_mul_residueDegree K L R)
  have hfin : ∀ q : MaximalSpectrum (R ⊗[K] L), q ∈ Finset.univ →
      Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) *
        (finiteAlgebraResidueDegree R (R ⊗[K] L) q : ℕ∞) ≠ ⊤ := fun q _ =>
    WithTop.mul_ne_top (fieldExtensionBaseChange_localLength_ne_top K L R q)
      (ENat.natCast_ne_top _)
  rw [ENat.toNat_sum hfin] at h
  simpa only [ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_sum, Nat.cast_mul] using
    congrArg (fun n : ℕ => (n : ℤ)) h

end Module
