/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.DimensionReduction
public import Motivic.Aglib.Algebra.Homology.LengthEuler.Single
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Lengths of actual Cartier cuts

A regular one-element Koszul complex computes the literal scalar quotient.
Finite homology supplies genuine finite quotient length before any integer
conversion. For quotient coefficients the third isomorphism theorem identifies
this module with the original ambient quotient by the cut and support ideals.
No reduction of the ambient ring or the closed support is taken.
-/

@[expose] public noncomputable section

open CategoryTheory HomologicalComplex _root_.HomologicalComplex.ModuleLengthEuler

universe u

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]

/-- Regularity identifies finite singleton Koszul homology with a finite-length
literal quotient. This assertion is independent of any `ENat.toNat` conversion. -/
theorem singleton_quotient_length_ne_top (M : ModuleCat R) (t : R)
    (ht : IsSMulRegular M t) (h : FiniteHomology (coefficientComplex M [t])) :
    Module.length R (SingleQuotient M t) ≠ ⊤ := by
  have hq := koszulDimensionReduction_finiteHomology M t [] ht h
  have he := (singleObjHomologySelfIso (ComplexShape.down ℕ) 0
    ((scalarQuotientFunctor t).obj M)).toLinearEquiv.length_eq
  exact he ▸ hq.finite_length 0

/-- The empty-list Koszul Euler test is the finite length of its coefficients. -/
theorem nil_chainEuler_eq_length (M : ModuleCat R) (hM : Module.length R M ≠ ⊤)
    (h : FiniteHomology (coefficientComplex M [])) :
    chainEuler (coefficientComplex M []) h = integerLength M hM := by
  simpa only [coefficientComplex_nil, pow_zero, one_mul] using
    homologyEuler_single (ComplexShape.down ℕ) 0 M (fun n : ℕ => (-1 : ℤ) ^ n) hM

/-- A regular singleton Koszul Euler characteristic is the actual finite
length of the scalar quotient, with arbitrary finite-homology evidence. -/
theorem singleton_chainEuler_eq_length (M : ModuleCat R) (t : R)
    (ht : IsSMulRegular M t) (h : FiniteHomology (coefficientComplex M [t])) :
    chainEuler (coefficientComplex M [t]) h =
      ((Module.length R (SingleQuotient M t)).toNat : ℤ) := by
  rw [koszulDimensionReduction_chainEuler M t [] ht h,
    nil_chainEuler_eq_length _ (singleton_quotient_length_ne_top M t ht h)]
  rfl

/-- Finite length of the literal scalar quotient is sufficient for finite
singleton Koszul homology when the scalar is regular. -/
theorem singleton_finiteHomology_of_regular (M : ModuleCat R) (t : R)
    (ht : IsSMulRegular M t) (hQ : Module.length R (SingleQuotient M t) ≠ ⊤) :
    FiniteHomology (coefficientComplex M [t]) := by
  have : QuasiIso (koszulDimensionReduction M t []) :=
    koszulDimensionReduction_quasiIso M t [] ht
  exact (finiteHomology_single (ComplexShape.down ℕ) 0
    ((scalarQuotientFunctor t).obj M) hQ).of_iso
      (fun n => (isoOfQuasiIsoAt (koszulDimensionReduction M t []) n).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scalar quotient of the original closed-support quotient is exactly
its ambient quotient by the support ideal and the singleton cut. -/
def singleQuotientQuotientEquiv (J : Ideal R) (t : R) :
    SingleQuotient (R ⧸ J) t ≃ₗ[R] R ⧸ (Ideal.ofList [t] ⊔ J) := by
  refine (Submodule.quotEquivOfEq _ _ ?_).trans
    ((Submodule.quotientQuotientEquivQuotientSup J (Ideal.ofList [t])).trans
      (Submodule.quotEquivOfEq _ _ (sup_comm _ _)))
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨t * z, ?_, rfl⟩
    exact Ideal.mul_mem_right _ _ (by simp)
  · rintro ⟨y, hy, rfl⟩
    change y ∈ (Ideal.ofList [t] : Ideal R) at hy
    have hy' : y ∈ Ideal.span {t} := by rw [← Ideal.ofList_singleton]; exact hy
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hy'
    exact ⟨Ideal.Quotient.mk J z, rfl⟩

/-- For ring coefficients the scalar quotient is the actual principal ideal quotient. -/
def singleQuotientRingEquiv (t : R) :
    SingleQuotient R t ≃ₗ[R] R ⧸ Ideal.ofList [t] :=
  Submodule.quotEquivOfEq _ _ (by
    ext x
    change (∃ y : R, t * y = x) ↔ x ∈ (Ideal.ofList [t] : Ideal R)
    rw [Ideal.ofList_singleton, Ideal.mem_span_singleton]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩)

/-- The regular ambient ring's singleton Euler test is its actual cut length. -/
theorem singleton_chainEuler_eq_ring_quotient_length (t : R) (ht : IsSMulRegular R t)
    (h : FiniteHomology (coefficientComplex (ModuleCat.of R R) [t])) :
    chainEuler (coefficientComplex (ModuleCat.of R R) [t]) h =
      ((Module.length R (R ⧸ Ideal.ofList [t])).toNat : ℤ) := by
  rw [singleton_chainEuler_eq_length (ModuleCat.of R R) t ht h,
    (singleQuotientRingEquiv t).length_eq]

/-- Genuine finite length of the original ambient Cartier-cut quotient. -/
theorem singleton_cut_length_ne_top (J : Ideal R) (t : R)
    (ht : IsSMulRegular (R ⧸ J) t)
    (h : FiniteHomology (coefficientComplex (ModuleCat.of R (R ⧸ J)) [t])) :
    Module.length R (R ⧸ (Ideal.ofList [t] ⊔ J)) ≠ ⊤ := by
  rw [← (singleQuotientQuotientEquiv J t).length_eq]
  exact singleton_quotient_length_ne_top (ModuleCat.of R (R ⧸ J)) t ht h

/-- A singleton Cartier-cut Euler test is the length of the actual cut of
its original support, including all nilpotent multiplicities. -/
theorem singleton_chainEuler_eq_quotient_length (J : Ideal R) (t : R)
    (ht : IsSMulRegular (R ⧸ J) t)
    (h : FiniteHomology (coefficientComplex (ModuleCat.of R (R ⧸ J)) [t])) :
    chainEuler (coefficientComplex (ModuleCat.of R (R ⧸ J)) [t]) h =
      ((Module.length R (R ⧸ (Ideal.ofList [t] ⊔ J))).toNat : ℤ) := by
  rw [singleton_chainEuler_eq_length (ModuleCat.of R (R ⧸ J)) t ht h,
    (singleQuotientQuotientEquiv J t).length_eq]

/-- An Artinian cut of the actual support supplies finite Koszul homology;
regularity is not needed for this finiteness assertion. -/
theorem singleton_quotient_finiteHomology_of_artinian [IsNoetherianRing R]
    (J : Ideal R) (t : R) [IsArtinianRing (R ⧸ (Ideal.ofList [t] ⊔ J))] :
    FiniteHomology (coefficientComplex (ModuleCat.of R (R ⧸ J)) [t]) :=
  finiteHomology_of_artinian_quotient_of_le_annihilator _ [t] J
    (by rw [Ideal.annihilator_quotient])

/-- Artinian support and scalar regularity give the actual quotient length. -/
theorem singleton_chainEuler_eq_quotient_length_of_artinian [IsNoetherianRing R]
    (J : Ideal R) (t : R) [IsArtinianRing (R ⧸ (Ideal.ofList [t] ⊔ J))]
    (ht : IsSMulRegular (R ⧸ J) t) :
    chainEuler (coefficientComplex (ModuleCat.of R (R ⧸ J)) [t])
        (singleton_quotient_finiteHomology_of_artinian J t) =
      ((Module.length R (R ⧸ (Ideal.ofList [t] ⊔ J))).toNat : ℤ) :=
  singleton_chainEuler_eq_quotient_length J t ht _

end ChainComplex.Koszul

namespace IsSMulRegular

variable {R : Type u} [CommRing R]

/-- A regular scalar stays regular on each original reduced component. No
reducedness of the ambient ring or flatness of its components is required. -/
theorem quotient_of_mem_minimalPrimes {t : R} (ht : IsSMulRegular R t)
    {p : Ideal R} (hp : p ∈ minimalPrimes R) : IsSMulRegular (R ⧸ p) t := by
  have hnz : t ∈ nonZeroDivisors R := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    exact ht (by simpa only [smul_eq_mul, mul_zero, mul_comm] using hx)
  have htp : t ∉ p := fun h =>
    Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp) h hnz
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem p t).mpr
  intro x hx
  exact (hp.isPrime.mem_or_mem hx).resolve_left htp

/-- The actual polynomial fiber parameter is regular on a flat algebra,
including nonreduced and non-domain flat algebras. -/
theorem polynomial_fiber_of_flat {k A : Type*} [CommRing k] [CommRing A]
    [Algebra (Polynomial k) A] [Module.Flat (Polynomial k) A] (a : k) :
    IsSMulRegular A (algebraMap (Polynomial k) A (Polynomial.X - Polynomial.C a)) :=
  (Polynomial.monic_X_sub_C a).isRegular.left.isSMulRegular.of_flat

end IsSMulRegular
