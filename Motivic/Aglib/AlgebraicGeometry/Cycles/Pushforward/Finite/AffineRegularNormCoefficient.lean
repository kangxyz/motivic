/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineNormPrincipalCoefficient
public import Motivic.Aglib.RingTheory.Multiplicity.Cartier.DVRDeterminantLength

/-!
# Regular norm coefficients for arbitrary finite free affine algebras

The whole localized source algebra may be disconnected or nonreduced. Only the
specified equation is required to be a non-zero-divisor. Every branch carries
the residue degree of the original scheme morphism.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineRegularNormCoefficient`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineRegularNormCycle`.
-/

open _root_.AlgebraicGeometry.Scheme.Hom.FiniteFiber
  (finiteAlgebraResidueDegree_eq_schemeResidueDegree)

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct nonZeroDivisors

universe u
namespace PrimeSpectrum.FiniteFiber

variable (A : CommRingCat.{u}) [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  (B : CommRingCat.{u}) [Algebra A B] [Module.Finite A B] [Module.Free A B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A regular equation has the original norm coefficient, with all branches and
actual residue degrees retained, without assuming the source algebra is a domain. -/
theorem localized_norm_coefficient_of_mem_nonZeroDivisors
    (p : PrimeSpectrum A) (hp : p.asIdeal.height = 1)
    (a : B) (ha : a ∈ nonZeroDivisors B) :
    letI := _root_.PrimeSpectrum.FiniteFiber.targetLocalization_isDiscreteValuationRing A p hp
    letI : Finite (MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)) :=
      Module.finiteAlgebra_maximalSpectrum_finite (Localization.AtPrime p.asIdeal)
        (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)
    letI := Fintype.ofFinite (MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p))
    IsDiscreteValuationRing.addVal (Localization.AtPrime p.asIdeal)
        (algebraMap A (Localization.AtPrime p.asIdeal) (Algebra.norm A a)) =
      ∑ q : MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p),
        _root_.PrimeSpectrum.FiniteFiber.localizedPrincipalQuotientLength (algebraMap B
            (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p) a) q *
        ((Spec.map (CommRingCat.ofHom (algebraMap A B) : A ⟶ B)).residueDegree
          (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1 : ℕ∞) := by
  let := _root_.PrimeSpectrum.FiniteFiber.targetLocalization_isDiscreteValuationRing A p hp
  have ha' : algebraMap B (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p) a ∈ nonZeroDivisors
      (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p) :=
    IsLocalization.nonZeroDivisors_le_comap
      (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl)
          (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p) ha
  have hi : Function.Injective
      (Algebra.lmul (Localization.AtPrime p.asIdeal) (_root_.PrimeSpectrum.FiniteFiber.localAlgebra
          A B p)
        (algebraMap B (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p) a)) :=
    (isRegular_iff_mem_nonZeroDivisors.mpr ha').1
  have hn := IsDiscreteValuationRing.addVal_norm_eq_fiberLengthSum_of_injective
    (R := Localization.AtPrime p.asIdeal) (algebraMap B
        (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p) a) hi
  change IsDiscreteValuationRing.addVal (Localization.AtPrime p.asIdeal)
      (Algebra.norm (Localization.AtPrime p.asIdeal) (1 ⊗ₜ[A] a)) = _ at hn
  rw [Algebra.norm_one_tmul] at hn
  rw [hn]
  unfold Module.finiteAlgebraFiberLengthSum
  apply Finset.sum_congr rfl
  intro q _
  rw [finiteAlgebraResidueDegree_eq_schemeResidueDegree A B p q]
  rfl

end PrimeSpectrum.FiniteFiber
