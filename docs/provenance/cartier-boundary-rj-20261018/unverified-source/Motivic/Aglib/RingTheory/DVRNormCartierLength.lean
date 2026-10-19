/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.DVRCartierLength
public import Motivic.RingTheory.LocalLength.FiniteAlgebraLength
public import Mathlib.LinearAlgebra.FreeModule.Norm
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Cartier quotient lengths and norms over a DVR

For a finite torsion-free domain algebra over a discrete valuation ring, the
length over the base of the actual principal quotient is the normalized order
of the determinant norm. Smith decomposition proves the statement without
perfectness, separability, normality of the algebra, or a chosen uniformizer.

The original finite-algebra length formula then expresses this order as the
sum of every localized quotient length times its actual residue degree. When
the algebra is normal, the existing integral norm is the same determinant
norm. These are local coefficient calculations, not a global
principal-divisor pushforward theorem.
-/

@[expose] public noncomputable section

namespace IsDiscreteValuationRing

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
  [Module.IsTorsionFree R S]

/-- The actual principal quotient length over the base DVR is the order of
the determinant norm. Nilpotent quotient structure and all source branches
are retained; no separability or perfectness hypothesis is needed. -/
theorem length_quotient_span_eq_addVal_norm (s : S) (hs : s ≠ 0) :
    Module.length R (S ⧸ Ideal.span {s}) = addVal R (Algebra.norm R s) := by
  classical
  let : Module.Free R S := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis R S
  let I : Ideal S := Ideal.span {s}
  have hI : I ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hs
  have hn := associated_norm_prod_smith b hs
  calc
    Module.length R (S ⧸ Ideal.span {s}) =
        Module.length R (∀ i, R ⧸ Ideal.span {I.smithCoeffs b hI i}) :=
      (I.quotientEquivPiSpan b hI).length_eq
    _ = ∑ i, Module.length R (R ⧸ Ideal.span {I.smithCoeffs b hI i}) :=
      Module.length_pi_of_fintype R _
    _ = ∑ i, addVal R (I.smithCoeffs b hI i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact length_quotient_span_eq_addVal _ (I.smithCoeffs_ne_zero b hI i)
    _ = addVal R (∏ i, I.smithCoeffs b hI i) := by
      exact (map_prod (addVal R) _ _).symm
    _ = addVal R (Algebra.norm R s) :=
      ((addVal_eq_iff_associated _ _).mpr hn).symm

/-- The norm order is the actual residue-degree-weighted sum of all localized
principal quotient lengths. Finiteness of these lengths follows from the
nonzero original equation, rather than being supplied as an extra premise. -/
theorem addVal_norm_eq_fiberLengthSum (s : S) (hs : s ≠ 0) :
    addVal R (Algebra.norm R s) =
      Motivic.LocalLength.finiteAlgebraFiberLengthSum
        (M := S ⧸ Ideal.span {s}) R S := by
  let : Module.Free R S := Module.free_of_finite_type_torsion_free'
  have hR : Module.length R (S ⧸ Ideal.span {s}) ≠ ⊤ := by
    rw [length_quotient_span_eq_addVal_norm s hs, ne_eq, addVal_eq_top_iff,
      Algebra.norm_eq_zero_iff]
    exact hs
  obtain ⟨hnoeth, hart⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hR)
  have : IsNoetherian S (S ⧸ Ideal.span {s}) := isNoetherian_of_tower R hnoeth
  have : IsArtinian S (S ⧸ Ideal.span {s}) := isArtinian_of_tower R hart
  rw [← length_quotient_span_eq_addVal_norm s hs]
  exact Motivic.LocalLength.finiteAlgebra_length_eq_fiberSum R S Module.length_ne_top

/-- For a normal finite torsion-free domain algebra, the same literal quotient
computes the order of the original integral norm, in arbitrary characteristic. -/
theorem length_quotient_span_eq_addVal_intNorm [IsIntegrallyClosed S]
    (s : S) (hs : s ≠ 0) :
    Module.length R (S ⧸ Ideal.span {s}) = addVal R (Algebra.intNorm R S s) := by
  let : Module.Free R S := Module.free_of_finite_type_torsion_free'
  rw [Algebra.intNorm_eq_norm]
  exact length_quotient_span_eq_addVal_norm s hs

/-- The original integral norm has the full local pushforward coefficient,
with all maximal branches and their actual residue degrees. -/
theorem addVal_intNorm_eq_fiberLengthSum [IsIntegrallyClosed S]
    (s : S) (hs : s ≠ 0) :
    addVal R (Algebra.intNorm R S s) =
      Motivic.LocalLength.finiteAlgebraFiberLengthSum
        (M := S ⧸ Ideal.span {s}) R S := by
  let : Module.Free R S := Module.free_of_finite_type_torsion_free'
  rw [Algebra.intNorm_eq_norm]
  exact addVal_norm_eq_fiberLengthSum s hs

end IsDiscreteValuationRing
