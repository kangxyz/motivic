/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Stalk.KernelMinimalPrimes
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Multiplicity.ClosedImmersionPointCoefficient
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Generic points and coefficients of an affine regular principal zero scheme

The zero scheme is the literal spectrum of the principal quotient, with its
original closed map. Regularity, rather than an integral ambient scheme, gives
codimension one. The full nonreduced fundamental cycle is retained, including
empty zero schemes and the zero ring. No replacement cycle is defined.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.AffineRegularPrincipalGenericity`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.AffineRegularPrincipalScalar`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme

variable (B : CommRingCat.{u}) [IsNoetherianRing B]
  (a : B) (ha : a ∈ nonZeroDivisors B)

include ha

/-- The actual primes of a regular principal quotient are generic exactly over
height-one ambient primes. The quotient and its nilpotents are unchanged. -/
theorem affine_regular_quotient_generic_iff
    (y : Spec (.of (B ⧸ Ideal.span {a}))) :
    y ∈ genericPoints (Spec (.of (B ⧸ Ideal.span {a}))) ↔
      (y.comap (Ideal.Quotient.mk (Ideal.span {a}))).asIdeal.height = 1 := by
  let I : Ideal B := Ideal.span {a}
  let q := y.asIdeal.comap (Ideal.Quotient.mk I)
  have hIq : I ≤ q := by
    rw [← Ideal.mk_ker (I := I)]
    exact Ideal.comap_mono bot_le
  have hlow : 1 ≤ I.height :=
    Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors ha
  have hmin : y.asIdeal ∈ minimalPrimes (B ⧸ I) ↔ q ∈ I.minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_comap]
    constructor
    · intro h
      exact ⟨y.asIdeal, h, rfl⟩
    · rintro ⟨q', hq', heq⟩
      have he : q' = y.asIdeal :=
        Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective heq
      exact he ▸ hq'
  rw [_root_.AlgebraicGeometry.Scheme.spec_mem_genericPoints_iff_minimalPrime]
  change y.asIdeal ∈ minimalPrimes (B ⧸ I) ↔ q.height = 1
  rw [hmin]
  constructor
  · intro hq
    exact le_antisymm
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I q hq)
      (hlow.trans (Ideal.height_mono hIq))
  · intro hq
    exact Ideal.mem_minimalPrimes_of_height_le hIq (hq.le.trans hlow)

open Classical in
/-- The pushed fundamental cycle of the literal regular principal quotient has
its original ambient-stalk quotient length at height one, and is zero elsewhere.
The actual closed map's kernel is retained, not replaced by its radical. -/
theorem affine_regular_quotient_fundamentalCoefficient (x : Spec B) :
    let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward i
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Spec (.of (B ⧸ Ideal.span {a}))))) x =
      if x.asIdeal.height = 1 then
        ((Module.length ((Spec B).presheaf.stalk x)
          (((Spec B).presheaf.stalk x) ⧸ i.ker.stalk x)).toNat : ℤ)
      else 0 := by
  classical
  dsimp only
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))
  by_cases hx : x.asIdeal.height = 1
  · rw [ite_eq_left hx]
    apply closedImmersion_fundamentalCoefficient_eq_length_at i x
    intro y hy
    apply (affine_regular_quotient_generic_iff B a ha y).mpr
    change (i y).asIdeal.height = 1
    simpa only [hy] using hx
  · rw [ite_eq_right hx]
    apply closedImmersion_fundamentalCoefficient_eq_zero_at i x
    intro y hy hg
    apply hx
    have hh := (affine_regular_quotient_generic_iff B a ha y).mp hg
    change (i y).asIdeal.height = 1 at hh
    simpa only [hy] using hh

end AlgebraicGeometry.Scheme
