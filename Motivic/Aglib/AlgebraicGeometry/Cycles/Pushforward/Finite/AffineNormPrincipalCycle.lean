/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineNormOrder
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.PrincipalOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Finite pushforward of the original affine principal-order cycle

The actual determinant norms and the original rational numerator and denominator
are retained. Support finiteness and codimension-one image preservation are
proved, not supplied. The scope is one finite-free domain chart; disconnected
normal sources and gluing norms across charts are separate integration steps.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineNormPrincipalCycle`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineRegularNormCycle`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Order

universe u
namespace AlgebraicGeometry.Scheme

/-- Every rational function defines the existing principal cycle on a unit neighborhood. -/
theorem exists_original_principalOrderCycle (X : Scheme.{u}) [IsIntegral X]
    [IsNoetherian X] (f : X.functionField) :
    ∃ c : _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle X, ∀ x, c x = X.ord f x := by
  by_cases hf : f = 0
  · exact ⟨0, fun x => by simp [hf]⟩
  obtain ⟨U, _, a, hU, ha, hunit⟩ := exists_isUnit_germ_eq X f hf
  let := hU
  refine ⟨_root_.AlgebraicGeometry.Scheme.principalOrderCycle U a hunit, fun x => ?_⟩
  rw [_root_.AlgebraicGeometry.Scheme.principalOrderCycle_apply, ha]

end AlgebraicGeometry.Scheme

namespace PrimeSpectrum.FiniteFiber

/-- The actual signed point cycle of the original affine rational ratio. -/
def affinePrincipalOrderCycle (R : CommRingCat.{u}) [IsDomain R] [IsNoetherianRing R]
    (a b : R) : _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle (Spec R) :=
  (_root_.AlgebraicGeometry.Scheme.exists_original_principalOrderCycle (Spec R)
    (_root_.PrimeSpectrum.FiniteFiber.affineFunction R a /
        _root_.PrimeSpectrum.FiniteFiber.affineFunction R b)).choose

@[simp] theorem affinePrincipalOrderCycle_apply
    (R : CommRingCat.{u}) [IsDomain R] [IsNoetherianRing R]
    (a b : R) (x : Spec R) :
    affinePrincipalOrderCycle R a b x =
      (Spec R).ord (_root_.PrimeSpectrum.FiniteFiber.affineFunction R a /
          _root_.PrimeSpectrum.FiniteFiber.affineFunction R b) x :=
  (_root_.AlgebraicGeometry.Scheme.exists_original_principalOrderCycle (Spec R)
    (_root_.PrimeSpectrum.FiniteFiber.affineFunction R a /
        _root_.PrimeSpectrum.FiniteFiber.affineFunction R b)).choose_spec x

variable (A B : CommRingCat.{u}) [IsDomain A] [IsNoetherianRing A]
  [IsDomain B] [Algebra A B] [Module.Finite A B] [Module.Free A B]

/-- A source height-one point maps to a target height-one point under the actual
finite-flat chart map. Going-down gives one inequality; integrality prevents
contraction to the zero prime. -/
theorem affine_image_height_one (x : PrimeSpectrum B) (hx : x.asIdeal.height = 1) :
    (x.comap (algebraMap A B)).asIdeal.height = 1 := by
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let p := x.asIdeal.under A
  have : p.IsPrime := Ideal.comap_isPrime _ _
  let : x.asIdeal.LiesOver p := ⟨rfl⟩
  have hle : p.height ≤ x.asIdeal.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p x.asIdeal]
    exact le_self_add
  have hne : p ≠ ⊥ := Ideal.IsIntegral.under_ne_bot A
    (x.asIdeal.ne_bot_of_height_eq_one hx)
  exact le_antisymm (hx ▸ hle)
    (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hne))

end PrimeSpectrum.FiniteFiber

namespace AlgebraicGeometry.Scheme

namespace FiniteSupportCycle

/-- A residue pushforward coefficient is the sum over its whole finite point fiber. -/
theorem residuePushforward_apply_finite_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    [Fintype {x : X // f x = y}] (c : _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle X) :
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward f c y =
      ∑ x : {x : X // f x = y}, c x.1 * (f.residueDegree x.1 : ℤ) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add, Finsupp.add_apply, hc, hd, add_mul, Finset.sum_add_distrib]
  | single x n =>
    rw [_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_single]
    by_cases hx : f x = y
    · let z : {x : X // f x = y} := ⟨x, hx⟩
      rw [Finset.sum_eq_single z]
      · simp [z, hx]
      · intro w _ hw
        have hne : x ≠ w.1 := by
          intro he
          apply hw
          exact Subtype.ext he.symm
        simp [hne]
      · simp
    · rw [Finsupp.single_apply, ite_eq_right (by exact hx)]
      symm
      apply Finset.sum_eq_zero
      intro w _
      have hne : x ≠ w.1 := fun h => hx (h ▸ w.2)
      simp [hne]

end FiniteSupportCycle

end AlgebraicGeometry.Scheme

namespace PrimeSpectrum.FiniteFiber

variable (A B : CommRingCat.{u}) [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  [IsDomain B] [Algebra A B] [Module.Finite A B] [Module.Free A B]

/-- The actual finite point-cycle pushforward of the original principal ratio
is the principal cycle of its determinant norm ratio, with every residue degree. -/
theorem residuePushforward_affinePrincipalOrderCycle
    (a b : B) (ha : a ≠ 0) (hb : b ≠ 0) :
    letI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
        (Spec.map (CommRingCat.ofHom (algebraMap A B) : A ⟶ B))
        (affinePrincipalOrderCycle B a b) =
      affinePrincipalOrderCycle A (Algebra.norm A a) (Algebra.norm A b) := by
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
  rw [_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_apply_finite_fiber
      f p, ← e.sum_comp]
  simp only [affinePrincipalOrderCycle_apply]
  by_cases hp : p.asIdeal.height = 1
  · exact (_root_.PrimeSpectrum.FiniteFiber.affine_ord_norm_ratio A B p hp a b ha hb).symm
  · have hp' : ¬ @coheight (Spec A) Scheme.instPreorderCarrierCarrierCommRingCat p = 1 := by
      rwa [← idealHeight_eq_coheight A p]
    rw [(Spec A).ord_eq_zero_of_coheight_neq_one hp']
    apply Finset.sum_eq_zero
    intro q _
    have hq : ¬ @coheight (Spec B) Scheme.instPreorderCarrierCarrierCommRingCat
        (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1 = 1 := by
      intro hq
      have hx : (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1.asIdeal.height = 1 :=
        (idealHeight_eq_coheight B _).trans hq
      have him := affine_image_height_one A B (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p
          q).1 hx
      rw [(_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).2] at him
      exact hp him
    change (Spec B).ord (_root_.PrimeSpectrum.FiniteFiber.affineFunction B a /
        _root_.PrimeSpectrum.FiniteFiber.affineFunction B b)
      (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1 * _ = 0
    rw [(Spec B).ord_eq_zero_of_coheight_neq_one hq, zero_mul]

end PrimeSpectrum.FiniteFiber

