/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.PolynomialFiberCycleSpecialization
public import Motivic.Aglib.AlgebraicGeometry.FiniteCurvePushforwardSpecialization
public import Motivic.Aglib.RingTheory.PrincipalKoszulEuler
public import Motivic.AlgebraicGeometry.Cycles.CodimensionOneDominance

/-!
# Original divisor-component endpoint coefficients

At an original point of a polynomial fiber, finite local cut length implies
actual genericity. The weighted whole fibers of the original reduced generic
components then compute the native principal Euler expression on the original
possibly nonreduced scheme's stalk. The component regularity premise excludes
components contained in the face; neither family flatness nor regularity on
the entire original stalk is assumed.

Applied to the actual numerator and denominator divisor schemes, these are
the separate geometric coefficient expressions needed by the signed face
comparison. Transport back to their common ambient stalk remains separate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Motivic Motivic.LengthEuler
open scoped BigOperators Polynomial

universe u

namespace AlgebraicGeometry.FiniteFlatCurve

variable {k : Type u} [Field k] {D : Scheme.{u}} [IsNoetherian D]
  (f : D ⟶ Spec (.of k[X])) (a : k)

omit [IsNoetherian D] in
/-- Finite length of the original local cut forces the original endpoint
point to be generic. No arbitrary-point coefficient/length equality is used. -/
theorem fiber_mem_genericPoints_of_cut_length (y : fiber f a)
    (hcut : Module.length (D.presheaf.stalk (fiberInclusion f a y))
      ((D.presheaf.stalk (fiberInclusion f a y)) ⧸
        Ideal.ofList [scalar f a (fiberInclusion f a y)]) ≠ ⊤) :
    y ∈ genericPoints (fiber f a) := by
  have hlen : Module.length ((fiber f a).presheaf.stalk y)
      ((fiber f a).presheaf.stalk y) ≠ ⊤ := by
    rwa [fiber_stalk_length f a y]
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp
    (Module.length_ne_top_iff.mp hlen)
  have : Ring.KrullDimLE 0 ((fiber f a).presheaf.stalk y) :=
    isArtinianRing_iff_krullDimLE_zero.mp inferInstance
  apply mem_genericPoints_of_coheight_eq_zero
  have hd : ringKrullDim ((fiber f a).presheaf.stalk y) = 0 :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  rw [ringKrullDim_stalk_eq_coheight] at hd
  exact_mod_cast hd

/-- The actual generic weights of the original divisor scheme, followed by
whole reduced-component fibers, give its native stalk principal Euler value.
The original divisor itself may be nonreduced and may have scalar torsion. -/
theorem weighted_component_fiber_coefficient_eq_principalEuler
    (y : fiber f a)
    (hcut : Module.length (D.presheaf.stalk (fiberInclusion f a y))
      ((D.presheaf.stalk (fiberInclusion f a y)) ⧸
        Ideal.ofList [scalar f a (fiberInclusion f a y)]) ≠ ⊤)
    (hregular : ∀ z : genericPoints D,
      IsSMulRegular ((D.presheaf.stalk (fiberInclusion f a y)) ⧸
        (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι.ker.stalk
          (fiberInclusion f a y)) (scalar f a (fiberInclusion f a y))) :
    let := IntegralCycle.genericPointFintype D
    ∑ z : genericPoints D, (genericMultiplicity z : ℤ) *
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward
          (fiberMap f a (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫
            fiberInclusion f a)
          (fundamentalCycle
            (fiber ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ f) a)))
        (fiberInclusion f a y) =
      Module.principalEuler (N := D.presheaf.stalk (fiberInclusion f a y))
        (scalar f a (fiberInclusion f a y)) := by
  classical
  let := IntegralCycle.genericPointFintype D
  have hy := fiber_mem_genericPoints_of_cut_length f a y hcut
  have hcoeff (z : genericPoints D) :
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward
          (fiberMap f a (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫
            fiberInclusion f a)
          (fundamentalCycle
            (fiber ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ f) a)))
        (fiberInclusion f a y) =
      ((Module.length (D.presheaf.stalk (fiberInclusion f a y))
        ((D.presheaf.stalk (fiberInclusion f a y)) ⧸
          (Ideal.ofList [scalar f a (fiberInclusion f a y)] ⊔
            (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι.ker.stalk
              (fiberInclusion f a y)))).toNat : ℤ) := by
    rw [closedImmersion_fundamentalCoefficient_eq_length_at _ _ ?_,
      fiberMap_composite_stalk]
    intro w hw
    have heq := (fiberInclusion f a).isEmbedding.injective hw
    change fiberMap f a (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι w = y
      at heq
    apply mem_genericPoints_of_preimmersion_image
      (fiberMap f a (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι)
    rwa [heq]
  simp_rw [hcoeff]
  let := scalar_cut_isArtinian_of_generic f a y hy
  have hEuler := chainEuler_eq_sum_of_fundamentalCycle_eq
    (fun z : genericPoints D => (IntegralClosedSubscheme.pointClosure z.1).val.subscheme)
    (fun z : genericPoints D => (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι)
    (fun z : genericPoints D => (genericMultiplicity z : ℤ))
    (fundamentalCycle_eq_sum_closed_components D)
    (fiberInclusion f a y) [scalar f a (fiberInclusion f a y)]
    (by intro r hr; simpa only [List.mem_singleton.mp hr] using
      scalar_mem_maximalIdeal f a y)
  rw [Koszul.singleton_ring_chainEuler_eq_principalEuler] at hEuler
  simp_rw [Koszul.singleton_chainEuler_eq_quotient_length _ _ (hregular _)] at hEuler
  exact hEuler.symm

end AlgebraicGeometry.FiniteFlatCurve
