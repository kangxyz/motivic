/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Pushforward.Finite.ResidueDegree
public import Motivic.Aglib.RingTheory.Multiplicity.Cartier.DVRNormLength
public import Aglib.RingTheory.PolynomialFiberNorm
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Original affine norm coefficients

The local calculation uses the whole finite algebra over a target localization,
not a source stalk assumed finite over that localization. Residue degrees are
those of the original affine scheme morphism. Conversion to signed scheme orders
and global cycle pushforward is separate from this whole-algebra length calculation.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineNormPrincipalCoefficient`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineNormStalkLength`,
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineRegularNormCoefficient`.
-/

open _root_.AlgebraicGeometry.Scheme.Hom.FiniteFiber
  (finiteAlgebraResidueDegree_eq_schemeResidueDegree)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct nonZeroDivisors

universe u
namespace PrimeSpectrum.FiniteFiber

variable (A : CommRingCat.{u}) [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

/-- A height-one target chart supplies its DVR; no DVR structure is assumed. -/
theorem targetLocalization_isDiscreteValuationRing (p : PrimeSpectrum A)
    (hp : p.asIdeal.height = 1) : IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) := by
  let R := Localization.AtPrime p.asIdeal
  have hdim : ringKrullDim R ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal R, hp]
    exact le_rfl
  let : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim
  let : Ring.DimensionLEOne R := ⟨fun {_} hne hprime =>
    (Ring.krullDimLE_one_iff_of_isPrime_bot.mp inferInstance) _ hne hprime⟩
  let : IsIntegrallyClosed R := isIntegrallyClosed_of_isLocalization R
    p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors
  let : IsDedekindDomain R :=
    (isDedekindDomain_iff R (FractionRing R)).mpr
      ⟨inferInstance, inferInstance, inferInstance,
        (isIntegrallyClosed_iff (FractionRing R)).mp inferInstance⟩
  exact ((IsDiscreteValuationRing.TFAE R
    (IsLocalization.AtPrime.not_isField A (p.asIdeal.ne_bot_of_height_eq_one hp) R)).out 1 3).mpr
      (inferInstance : IsDedekindDomain R)

variable (B : CommRingCat.{u}) [IsDomain B] [Algebra A B]
  [Module.Finite A B] [Module.Free A B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The full principal quotient localized at a specified maximal branch. -/
def localizedPrincipalQuotientLength {S : Type u} [CommRing S]
    (a : S) (q : MaximalSpectrum S) : ℕ∞ :=
  Module.length (Localization.AtPrime q.asIdeal)
    (Localization.AtPrime q.asIdeal ⊗[S] (S ⧸ Ideal.span {a}))

/-- The original determinant norm has the full localized coefficient, including
all actual source residue degrees. The summands are localized modules of the
original principal quotient, before any conversion to scheme orders. -/
theorem localized_norm_coefficient (p : PrimeSpectrum A) (hp : p.asIdeal.height = 1)
    (a : B) (ha : a ≠ 0) :
    letI := targetLocalization_isDiscreteValuationRing A p hp
    letI : Finite (MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)) :=
      Module.finiteAlgebra_maximalSpectrum_finite (Localization.AtPrime p.asIdeal)
        (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)
    letI := Fintype.ofFinite (MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p))
    IsDiscreteValuationRing.addVal (Localization.AtPrime p.asIdeal)
        (algebraMap A (Localization.AtPrime p.asIdeal) (Algebra.norm A a)) =
      ∑ q : MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p),
        localizedPrincipalQuotientLength (algebraMap B
            (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p) a) q *
        ((Spec.map (CommRingCat.ofHom (algebraMap A B) : A ⟶ B)).residueDegree
          (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1 : ℕ∞) := by
  let := targetLocalization_isDiscreteValuationRing A p hp
  have hden : Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl ≤ nonZeroDivisors B :=
    map_le_nonZeroDivisors_of_injective (algebraMap A B)
      (FaithfulSMul.algebraMap_injective A B) p.asIdeal.primeCompl_le_nonZeroDivisors
  let : IsDomain (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ hden
  have ha' : algebraMap B (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p) a ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective _ hden)).mpr ha
  have hn := IsDiscreteValuationRing.addVal_norm_eq_fiberLengthSum
    (R := Localization.AtPrime p.asIdeal) (algebraMap B
        (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p) a) ha'
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
