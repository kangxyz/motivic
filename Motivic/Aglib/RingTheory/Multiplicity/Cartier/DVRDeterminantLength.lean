/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DVRCartierLength
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.LinearAlgebra.Determinant
public import Aglib.RingTheory.FiniteLength.FiniteAlgebraLength
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Determinant order and cokernel length over a DVR

An injective endomorphism of a finite free module has cokernel length equal
to the normalized order of its determinant. The module need not be an algebra
or a domain; Smith decomposition is applied to the whole image submodule.


Intended upstream module: `Aglib.RingTheory.Multiplicity.Cartier.DVRDeterminantLength`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineRegularNormCoefficient`.
-/

@[expose] public noncomputable section

open Module

namespace IsDiscreteValuationRing

variable {R M : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

/-- The literal cokernel of an injective endomorphism has length equal to the
normalized DVR order of its determinant. -/
theorem length_quotient_range_eq_addVal_det (f : M →ₗ[R] M)
    (hf : Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by
  classical
  let b := Module.Free.chooseBasis R M
  let N := LinearMap.range f
  let e := LinearEquiv.ofInjective f hf
  have h : Module.finrank R N = Module.finrank R M := e.finrank_eq.symm
  let bt := N.smithNormalFormTopBasis b h
  let bb := N.smithNormalFormBotBasis b h
  let a := N.smithNormalFormCoeffs b h
  let es : M ≃ₗ[R] N := bt.equiv bb (Equiv.refl _)
  have hd : N.subtype ∘ₗ es.toLinearMap = Matrix.toLin bt bt (Matrix.diagonal a) := by
    apply bt.ext
    intro i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, es, Basis.equiv_apply,
      Equiv.refl_apply, Submodule.subtype_apply]
    rw [Submodule.smithNormalFormBotBasis_def]
    simp [Matrix.toLin_apply, Basis.repr_self, Finsupp.single_eq_pi_single,
      bt, a]
  have ha : Associated (LinearMap.det f) (∏ i, a i) := by
    have he : N.subtype ∘ₗ e.toLinearMap = f := by ext x; rfl
    have hh := LinearMap.associated_det_comp_equiv N.subtype e es
    rw [he, hd, LinearMap.det_toLin, Matrix.det_diagonal] at hh
    exact hh
  calc
    Module.length R (M ⧸ N) = Module.length R (∀ i, R ⧸ Ideal.span {a i}) :=
      (N.quotientEquivPiSpan b h).length_eq
    _ = ∑ i, Module.length R (R ⧸ Ideal.span {a i}) := Module.length_pi_of_fintype R _
    _ = ∑ i, addVal R (a i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact length_quotient_span_eq_addVal _ (N.smithNormalFormCoeffs_ne_zero b h i)
    _ = addVal R (∏ i, a i) := by
      symm
      induction (Finset.univ : Finset (Module.Free.ChooseBasisIndex R M)) using
          Finset.induction_on with
      | empty => simp
      | @insert i t hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi, AddValuation.map_mul, ih]
    _ = addVal R (LinearMap.det f) :=
      ((addVal_eq_iff_associated _ _).mpr ha).symm

section Algebra

variable {S : Type*} [CommRing S] [Algebra R S] [Module.Finite R S]
  [Module.IsTorsionFree R S]

/-- A regular element in a finite torsion-free algebra has principal quotient
length equal to its determinant norm order. The algebra may be disconnected. -/
theorem length_quotient_span_eq_addVal_norm_of_injective (s : S)
    (hs : Function.Injective (Algebra.lmul R S s)) :
    Module.length R (S ⧸ Ideal.span {s}) = addVal R (Algebra.norm R s) := by
  let : Module.Free R S := Module.free_of_finite_type_torsion_free'
  have h := length_quotient_range_eq_addVal_det (Algebra.lmul R S s) hs
  have hr : LinearMap.range (Algebra.lmul R S s) =
      (Ideal.span {s}).restrictScalars R := Ideal.range_mul (R := R) S s
  rw [hr] at h
  exact h

/-- Every maximal branch of the literal principal quotient contributes its
localized length times its residue degree, without a source-domain premise. -/
theorem addVal_norm_eq_fiberLengthSum_of_injective (s : S)
    (hs : Function.Injective (Algebra.lmul R S s)) :
    addVal R (Algebra.norm R s) =
      Module.finiteAlgebraFiberLengthSum (M := S ⧸ Ideal.span {s}) R S := by
  let : Module.Free R S := Module.free_of_finite_type_torsion_free'
  have hn : Algebra.norm R s ≠ 0 := by
    rw [Algebra.norm_apply, ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot]
    exact not_not.mpr (LinearMap.ker_eq_bot.mpr hs)
  have hR : Module.length R (S ⧸ Ideal.span {s}) ≠ ⊤ := by
    rw [length_quotient_span_eq_addVal_norm_of_injective s hs, ne_eq, addVal_eq_top_iff]
    exact hn
  obtain ⟨hnoeth, hart⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hR)
  have : IsNoetherian S (S ⧸ Ideal.span {s}) := isNoetherian_of_tower R hnoeth
  have : IsArtinian S (S ⧸ Ideal.span {s}) := isArtinian_of_tower R hart
  rw [← length_quotient_span_eq_addVal_norm_of_injective s hs]
  exact Module.finiteAlgebra_length_eq_fiberSum R S Module.length_ne_top

end Algebra

end IsDiscreteValuationRing
