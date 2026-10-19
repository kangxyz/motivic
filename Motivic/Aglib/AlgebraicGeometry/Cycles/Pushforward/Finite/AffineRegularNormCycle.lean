/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.AffineRegularPrincipalScalar
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineRegularNormCoefficient
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineNormPrincipalCycle
public import Motivic.Aglib.RingTheory.Ideal.GoingDown.Height

/-!
# Norm pushforward of whole affine regular Cartier cycles

The source is the difference of the literal pushed fundamental cycles of the
original principal quotients. It may be disconnected or nonreduced. Only the
base is a normal Noetherian domain, and the whole source algebra is finite free.
No function field of the source or freeness of individual components is used.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineRegularNormCycle`.
Incoming project consumers: `Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.AffineNormCycle`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u
namespace PrimeSpectrum.FiniteFiber

variable (A : CommRingCat.{u}) [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  (B : CommRingCat.{u}) [Algebra A B] [Module.Finite A B] [Module.Free A B]

omit [IsNoetherianRing A] [IsIntegrallyClosed A] in
private theorem regular_norm_ne_zero (a : B) (ha : a ∈ nonZeroDivisors B) :
    Algebra.norm A a ≠ 0 := by
  rw [Algebra.norm_apply, ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot]
  exact not_not.mpr (LinearMap.ker_eq_bot.mpr
    (isRegular_iff_mem_nonZeroDivisors.mpr ha).1)

private theorem regular_quotient_coefficient
    [IsNoetherianRing B] (a : B) (ha : a ∈ nonZeroDivisors B) (x : Spec B)
    (hx : x.asIdeal.height = 1) :
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))))
        (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Spec (.of (B ⧸ Ideal.span {a})))) x
            =
      ((Module.length ((Spec B).presheaf.stalk x)
        (((Spec B).presheaf.stalk x) ⧸ Ideal.span {
          (Spec B).presheaf.germ ⊤ x (by trivial) ((Scheme.ΓSpecIso B).inv a)})).toNat : ℤ) := by
  have h := _root_.AlgebraicGeometry.Scheme.affine_regular_quotient_fundamentalCoefficient_scalar B
      a ha x
  rw [_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply,
      _root_.AlgebraicGeometry.Scheme.toPoints_fundamentalCycle,
    ite_eq_left hx] at h
  exact h

/-- A whole regular principal zero scheme pushes forward to the existing
principal cycle of its actual determinant norm. Empty source algebras are allowed. -/
theorem residuePushforward_regular_quotient (a : B) (ha : a ∈ nonZeroDivisors B) :
    letI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
        (Spec.map (CommRingCat.ofHom (algebraMap A B) : A ⟶ B))
        (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))))
          (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Spec (.of (B ⧸ Ideal.span {a})))))
              =
      _root_.PrimeSpectrum.FiniteFiber.affinePrincipalOrderCycle A (Algebra.norm A a) 1 := by
  classical
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let f := Spec.map (CommRingCat.ofHom (algebraMap A B) : A ⟶ B)
  ext p
  let : Finite (MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)) :=
    Module.finiteAlgebra_maximalSpectrum_finite (Localization.AtPrime p.asIdeal)
      (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)
  let := Fintype.ofFinite (MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p))
  let e : MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p) ≃ {x : Spec B // f x
      = p} :=
    _root_.PrimeSpectrum.FiniteFiber.maximalSpectrumEquivFiber A B p
  let : Fintype {x : Spec B // f x = p} := Fintype.ofEquiv _ e
  rw [_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_apply_finite_fiber f p,
      ← e.sum_comp,
    _root_.PrimeSpectrum.FiniteFiber.affinePrincipalOrderCycle_apply]
  have hone : _root_.PrimeSpectrum.FiniteFiber.affineFunction A 1 = 1 := by simp
      [_root_.PrimeSpectrum.FiniteFiber.affineFunction]
  rw [hone, div_one]
  have hheight (q : MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)) :
      (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1.asIdeal.height = p.asIdeal.height :=
          by
    have h := PrimeSpectrum.height_comap_eq_of_finite_flat A B
        (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1
    rw [(_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).2] at h
    exact h.symm
  by_cases hp : p.asIdeal.height = 1
  · let := _root_.PrimeSpectrum.FiniteFiber.targetLocalization_isDiscreteValuationRing A p hp
    have hn := _root_.PrimeSpectrum.FiniteFiber.localized_norm_coefficient_of_mem_nonZeroDivisors A
        B p hp a ha
    have hnorm : algebraMap A (Localization.AtPrime p.asIdeal) (Algebra.norm A a) ≠ 0 :=
      (map_ne_zero_iff _
        (IsLocalization.injective _ p.asIdeal.primeCompl_le_nonZeroDivisors)).mpr
        (regular_norm_ne_zero A B a ha)
    have hsum : (∑ q : MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p),
        _root_.PrimeSpectrum.FiniteFiber.localizedPrincipalQuotientLength (algebraMap B
            (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p) a) q *
          (f.residueDegree (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1 : ℕ∞)) ≠ ⊤ := by
      rw [← hn]
      exact IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hnorm
    have hnat := congrArg ENat.toNat hn
    rw [ENat.toNat_sum (fun q hq => ne_top_of_le_ne_top hsum
      (Finset.single_le_sum (fun _ _ => zero_le) hq))] at hnat
    rw [_root_.PrimeSpectrum.FiniteFiber.affine_ord_eq_length A p hp _ (regular_norm_ne_zero A B a
        ha),
      IsDiscreteValuationRing.length_quotient_span_eq_addVal _ hnorm,
      hnat, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro q _
    simp only [ENat.toNat_mul, Nat.cast_mul, ENat.toNat_natCast]
    rw [_root_.PrimeSpectrum.FiniteFiber.localizedPrincipalQuotientLength_eq_source_stalk]
    have he : (e q).1 = (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1 := rfl
    rw [he, regular_quotient_coefficient B a ha _ ((hheight q).trans hp)]
  · have hp' : ¬ @Order.coheight (Spec A) Scheme.instPreorderCarrierCarrierCommRingCat p = 1 := by
      rwa [← idealHeight_eq_coheight A p]
    rw [(Spec A).ord_eq_zero_of_coheight_neq_one hp']
    apply Finset.sum_eq_zero
    intro q _
    have hx : (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1.asIdeal.height ≠ 1 := by
      rwa [hheight q]
    have h := _root_.AlgebraicGeometry.Scheme.affine_regular_quotient_fundamentalCoefficient_scalar
        B a ha
      (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1
    rw [_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply,
        _root_.AlgebraicGeometry.Scheme.toPoints_fundamentalCycle,
      ite_eq_right hx] at h
    have he : (e q).1 = (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1 := rfl
    rw [he, h, zero_mul]

/-- Finite pushforward of the literal regular Cartier numerator-minus-denominator
cycle equals the existing principal cycle of the actual determinant norm ratio. -/
theorem residuePushforward_regular_cartier_norm_ratio
    (a b : B) (ha : a ∈ nonZeroDivisors B) (hb : b ∈ nonZeroDivisors B) :
    letI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
        (Spec.map (CommRingCat.ofHom (algebraMap A B) : A ⟶ B))
        (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))))
            (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Spec (.of (B ⧸ Ideal.span
                {a})))) -
          _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))))
            (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Spec (.of (B ⧸ Ideal.span
                {b}))))) =
      _root_.PrimeSpectrum.FiniteFiber.affinePrincipalOrderCycle A (Algebra.norm A a) (Algebra.norm
          A b) := by
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  rw [map_sub, residuePushforward_regular_quotient A B a ha,
    residuePushforward_regular_quotient A B b hb]
  ext p
  simp only [Finsupp.sub_apply, _root_.PrimeSpectrum.FiniteFiber.affinePrincipalOrderCycle_apply]
  have hone : _root_.PrimeSpectrum.FiniteFiber.affineFunction A 1 = 1 := by simp
      [_root_.PrimeSpectrum.FiniteFiber.affineFunction]
  rw [hone, div_one, div_one]
  have h := (Spec A).ord_add_ord_ratio
    (_root_.PrimeSpectrum.FiniteFiber.affineFunction A (Algebra.norm A b))
        (_root_.PrimeSpectrum.FiniteFiber.affineFunction A (Algebra.norm A a))
    (_root_.PrimeSpectrum.FiniteFiber.affineFunction_ne_zero A _ (regular_norm_ne_zero A B b hb))
    (_root_.PrimeSpectrum.FiniteFiber.affineFunction_ne_zero A _ (regular_norm_ne_zero A B a ha)) p
  exact (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)).symm

end PrimeSpectrum.FiniteFiber
