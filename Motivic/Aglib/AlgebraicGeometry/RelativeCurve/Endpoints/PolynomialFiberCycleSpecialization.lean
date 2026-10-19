/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Multiplicity.ClosedImmersionPointCoefficient
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.ComponentRegularity

/-!
# Whole polynomial-fiber cycles from generic support preservation

A singleton Euler test at each actual generic point of the whole endpoint
fiber retains its full scheme-theoretic length. Proven preservation of generic
points by the component fiber maps rules out all off-generic coefficients.
Thus the original component multiplicities specialize without requiring the
whole family to be finite over the affine line. This module uses the project's
cycle and Koszul infrastructure; it is not a standalone upstream Aglib import.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits _root_.HomologicalComplex.ModuleLengthEuler
open scoped BigOperators Polynomial

universe u

namespace AlgebraicGeometry.FiniteFlatCurve
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom
open _root_.ChainComplex

variable {k : Type u} [Field k] {P : Scheme.{u}}
  (f : P ⟶ Spec (.of k[X])) (a : k)

/-- The original singleton quotient is Artinian at an actual generic point of
the whole endpoint fiber, even when the fiber is positive dimensional. -/
theorem scalar_cut_isArtinian_of_generic [IsNoetherian P]
    (y : fiber f a) (hy : y ∈ genericPoints (fiber f a)) :
    IsArtinianRing ((P.presheaf.stalk (fiberInclusion f a y)) ⧸
      (Ideal.ofList [scalar f a (fiberInclusion f a y)] ⊔ ⊥)) := by
  rw [sup_bot_eq, ← fiberInclusion_stalk, Scheme.Hom.ker_stalk]
  exact stalk_quotient_ker_isArtinian (fiberInclusion f a) y hy

/-- The weighted original component formula specializes to the entire fiber.
The support premise is only generic-point preservation, not a cycle equality;
finite-flat relative geometry supplies it in the downstream endpoint theorem. -/
theorem fundamentalCycle_specialization_of_generic_preservation
    [Flat f] [IsNoetherian P]
    (hgeneric : ∀ (z : genericPoints P)
      (w : fiber ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ f) a),
      w ∈ genericPoints (fiber
        ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ f) a) →
      fiberMap f a (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι w ∈
        genericPoints (fiber f a)) :
    let := IntegralCycle.genericPointFintype P
    fundamentalCycle (fiber f a) =
      ∑ z : genericPoints P, (genericMultiplicity z : ℤ) •
        IntegralCycle.finitePushforward
          (fiberMap f a (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι)
          (fundamentalCycle
            (fiber ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ f) a)) := by
  classical
  let := IntegralCycle.genericPointFintype P
  apply IntegralCycle.finitePushforward_injective_of_isClosedImmersion (fiberInclusion f a)
  rw [map_sum]
  simp_rw [map_zsmul]
  have hcomp (z : genericPoints P) :
      IntegralCycle.finitePushforward (fiberInclusion f a)
          (IntegralCycle.finitePushforward
            (fiberMap f a (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι)
            (fundamentalCycle
              (fiber ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ f) a))) =
        IntegralCycle.finitePushforward
          (fiberMap f a (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫
            fiberInclusion f a)
          (fundamentalCycle
            (fiber ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ f) a)) := by
    rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
  simp_rw [hcomp]
  apply IntegralCycle.toPoints_injective
  ext x
  simp only [map_sum, map_zsmul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    zsmul_eq_mul, Int.cast_id]
  by_cases hx : x ∈ Set.range (fiberInclusion f a)
  · obtain ⟨y, rfl⟩ := hx
    by_cases hy : y ∈ genericPoints (fiber f a)
    · rw [closedImmersion_fundamentalCoefficient_eq_length_at (fiberInclusion f a) _
        (fun v hv ↦ (fiberInclusion f a).isEmbedding.injective hv ▸ hy)]
      have hcoeff (z : genericPoints P) :
          IntegralCycle.toPoints (IntegralCycle.finitePushforward
              (fiberMap f a (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫
                fiberInclusion f a)
              (fundamentalCycle
                (fiber ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ f) a)))
              (fiberInclusion f a y) =
            ((Module.length (P.presheaf.stalk (fiberInclusion f a y))
              ((P.presheaf.stalk (fiberInclusion f a y)) ⧸
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
        (fun z : genericPoints P => (IntegralClosedSubscheme.pointClosure z.1).val.subscheme)
        (fun z : genericPoints P => (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι)
        (fun z : genericPoints P => (genericMultiplicity z : ℤ))
        (fundamentalCycle_eq_sum_closed_components P)
        (fiberInclusion f a y) [scalar f a (fiberInclusion f a y)]
        (by intro r hr; simpa only [List.mem_singleton.mp hr] using
          scalar_mem_maximalIdeal f a y)
      rw [Koszul.singleton_chainEuler_eq_ring_quotient_length
        _ (scalar_regular f a _)] at hEuler
      simp_rw [Koszul.singleton_chainEuler_eq_quotient_length
        _ _ (flat_polynomial_component_quotient_scalar_regular f _ a _)] at hEuler
      rw [fiberInclusion_stalk f a (fiberInclusion f a y)]
      exact hEuler
    · rw [closedImmersion_fundamentalCoefficient_eq_zero_at (fiberInclusion f a) _
        (fun v hv ↦ (fiberInclusion f a).isEmbedding.injective hv ▸ hy)]
      symm
      apply Finset.sum_eq_zero
      intro z _
      rw [closedImmersion_fundamentalCoefficient_eq_zero_at _ _ ?_, mul_zero]
      intro w hw hwgen
      apply hy
      have heq := (fiberInclusion f a).isEmbedding.injective hw
      change fiberMap f a (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι w = y
        at heq
      rw [← heq]
      exact hgeneric z w hwgen
  · rw [closedImmersion_fundamentalCoefficient_eq_zero_at (fiberInclusion f a) _
      (fun y hy ↦ (hx ⟨y, hy⟩).elim)]
    symm
    apply Finset.sum_eq_zero
    intro z _
    rw [closedImmersion_fundamentalCoefficient_eq_zero_at _ _ ?_, mul_zero]
    intro w hw
    exact (hx ⟨fiberMap f a (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι w,
      hw⟩).elim

end AlgebraicGeometry.FiniteFlatCurve
