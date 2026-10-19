/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Flat.PolynomialGeneric
public import Aglib.RingTheory.IntegralClosure.FiniteEtale

/-!
# Coefficient-localized finite flatness of polynomial normalizations

Original polynomial torsion-freeness supplies the generic torsion-freeness
required by basis descent. For a normal Noetherian polynomial ring, the literal
integral closure in an etale fraction-field algebra satisfies both finiteness
and torsion-freeness. The ambient algebra may be a product or zero: no domain
hypothesis on it is imposed.

The output is the canonical coefficient-localized Spec projection of that
integral closure. Transport along a particular scheme normalization chart and
combining the two projective-line charts remain separate geometric steps.


Intended upstream module: `Aglib.AlgebraicGeometry.Normalization.FiniteCurve.PolynomialFiniteFlat`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Normalization.FiniteCurve.PolynomialChartFiniteFlat`.
-/

@[expose] public noncomputable section

open scoped Polynomial TensorProduct nonZeroDivisors

attribute [local instance] Polynomial.algebra

namespace AlgebraicGeometry

universe u

/-- Original polynomial torsion-freeness suffices for finite flatness after
inverting one nonzero coefficient, without a separately supplied generic-fiber
module hypothesis. -/
theorem exists_finite_flat_polynomial_specMap_away_of_isTorsionFree
    (R K B : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing B] [Algebra R[X] B]
    [Module.FinitePresentation R[X] B] [Module.IsTorsionFree R[X] B] :
    ∃ r : R, r ≠ 0 ∧
      IsFinite (Spec.map (CommRingCat.ofHom
        (R := (Localization.Away r)[X]) (S := (Localization.Away r)[X] ⊗[R[X]] B)
        (algebraMap (Localization.Away r)[X] ((Localization.Away r)[X] ⊗[R[X]] B)))) ∧
      Flat (Spec.map (CommRingCat.ofHom
        (R := (Localization.Away r)[X]) (S := (Localization.Away r)[X] ⊗[R[X]] B)
        (algebraMap (Localization.Away r)[X] ((Localization.Away r)[X] ⊗[R[X]] B)))) := by
  let S : Submonoid R[X] := R⁰.map Polynomial.C
  let : IsLocalization S K[X] := Polynomial.isLocalization R⁰ K
  let : Module.IsTorsionFree K[X] (K[X] ⊗[R[X]] B) :=
    IsLocalizedModule.isTorsionFree (TensorProduct.mk R[X] K[X] B 1) S
  obtain ⟨r, hr, _, hfinite, hflat⟩ := exists_finite_flat_polynomial_specMap_away R K B
  exact ⟨r, hr, hfinite, hflat⟩

/-- The actual integral closure in an etale algebra over the fraction field of
`R[X]` becomes finite flat after one nonzero coefficient localization. Normality
and Noetherianity belong to the polynomial base; no domain assumption is made
on the etale algebra or on its integral closure. -/
theorem exists_finite_flat_polynomial_integralClosure_specMap_away
    (R K L E : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [IsNoetherianRing R[X]] [IsIntegrallyClosed R[X]]
    [Field L] [Algebra R[X] L] [IsFractionRing R[X] L]
    [CommRing E] [Algebra L E] [Algebra R[X] E] [IsScalarTower R[X] L E]
    [Algebra.Etale L E] :
    ∃ r : R, r ≠ 0 ∧
      IsFinite (Spec.map (CommRingCat.ofHom
        (R := (Localization.Away r)[X])
        (S := (Localization.Away r)[X] ⊗[R[X]] integralClosure R[X] E)
        (algebraMap (Localization.Away r)[X]
          ((Localization.Away r)[X] ⊗[R[X]] integralClosure R[X] E)))) ∧
      Flat (Spec.map (CommRingCat.ofHom
        (R := (Localization.Away r)[X])
        (S := (Localization.Away r)[X] ⊗[R[X]] integralClosure R[X] E)
        (algebraMap (Localization.Away r)[X]
          ((Localization.Away r)[X] ⊗[R[X]] integralClosure R[X] E)))) := by
  let : Module.IsTorsionFree R[X] L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (IsFractionRing.injective R[X] L)
  let : Module.IsTorsionFree R[X] E := Module.IsTorsionFree.trans L
  let : Module.Finite R[X] (integralClosure R[X] E) :=
    integralClosure.finite_of_etale R[X] L E
  let : Module.FinitePresentation R[X] (integralClosure R[X] E) :=
    Module.finitePresentation_of_finite R[X] (integralClosure R[X] E)
  exact exists_finite_flat_polynomial_specMap_away_of_isTorsionFree R K
    (integralClosure R[X] E)

end AlgebraicGeometry
