/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.LocalLength.FiniteAlgebraLength
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Artinian.Ring

/-!
# Dimensions of all branches of a monic polynomial quotient

The dimension of the whole quotient is the sum of its original local
self-lengths weighted by the dimensions of its literal maximal quotients.
This includes nonreduced algebras and inseparable or nontrivial residue
extensions. No scalar-root or polynomial-factorization hypothesis is used.
-/

@[expose] public noncomputable section

open Polynomial
open scoped BigOperators TensorProduct

namespace Algebra

universe u v

variable {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B]
  [Module.Finite k B]

/-- The dimension of a finite algebra counts every maximal quotient with the
self-length of the original localization, retaining all nilpotents. -/
theorem finrank_eq_sum_local_length_mul_finrank [Fintype (MaximalSpectrum B)] :
    Module.finrank k B = ∑ q : MaximalSpectrum B,
      (Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat * Module.finrank k (B ⧸ q.asIdeal) := by
  let : IsArtinianRing B := .of_finite k B
  have h := Motivic.LocalLength.finiteAlgebra_length_eq_sum
    (R := k) (S := B) (M := B) Module.length_ne_top
  have hlocal (q : MaximalSpectrum B) :
      Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal ⊗[B] B) =
      Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) :=
    (TensorProduct.AlgebraTensorModule.rid B
      (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).length_eq
  have hdeg (q : MaximalSpectrum B) :
      (Motivic.LocalLength.finiteAlgebraResidueDegree k B q : ℕ∞) =
        (Module.finrank k (B ⧸ q.asIdeal) : ℕ∞) := by
    rw [← Motivic.LocalLength.finiteAlgebra_residue_length k B q,
      Module.length_eq_finrank]
  have hn (q : MaximalSpectrum B) :
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℕ∞) =
      Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) :=
    ENat.natCast_toNat Module.length_ne_top
  apply ENat.natCast_inj.mp
  push_cast
  simpa only [Module.length_eq_finrank, hlocal, hdeg, hn] using h

end Algebra

namespace AdjoinRoot

universe u

variable {k : Type u} [Field k]

/-- Every branch of the whole monic polynomial quotient contributes its
original local self-length times its residue degree, totaling the polynomial
degree. No reduction, separability, irreducibility or scalar-root assumption
is imposed. -/
theorem sum_local_length_mul_finrank_eq_natDegree (p : k[X]) (hp : p.Monic) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    ∑ q : MaximalSpectrum (AdjoinRoot p),
      (Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat *
          Module.finrank k (AdjoinRoot p ⧸ q.asIdeal) = p.natDegree := by
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  exact (Algebra.finrank_eq_sum_local_length_mul_finrank (k := k)
    (B := AdjoinRoot p)).symm.trans finrank_quotient_span_eq_natDegree

end AdjoinRoot
