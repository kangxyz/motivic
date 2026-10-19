/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Endpoints.FiniteFlatCurveSpecialization

/-!
# Consumers of actual finite-flat curve specialization

The family is arbitrary, including nilpotents and disconnected components.
The field is arbitrary, with no perfection or algebraic-closure condition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve
open scoped BigOperators Polynomial

universe u

namespace MotivicTest.FiniteFlatCurveSpecialization

variable {k : Type u} [Field k] {P : Scheme.{u}}
  (f : P ⟶ Spec (.of k[X])) [IsFinite f] [Flat f] [IsNoetherian P]

/-- Every original generic length weights its entire actual endpoint fiber. -/
theorem arbitraryFiniteFlatCurve (a : k) :
    let := _root_.AlgebraicGeometry.Scheme.IntegralCycle.genericPointFintype P
    _root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber f a) =
      ∑ z : genericPoints P, (_root_.AlgebraicGeometry.Scheme.genericMultiplicity z : ℤ) •
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward
          (fiberMap f a (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
              z.1).val.subschemeι)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle
            (fiber ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
                z.1).val.subschemeι ≫ f) a)) :=
  finiteFlatCurve_fundamentalCycle_specialization f a

/-- The literal zero endpoint uses the same theorem and original component weights. -/
theorem zeroEndpoint :
    let := _root_.AlgebraicGeometry.Scheme.IntegralCycle.genericPointFintype P
    _root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber f (0 : k)) =
      ∑ z : genericPoints P, (_root_.AlgebraicGeometry.Scheme.genericMultiplicity z : ℤ) •
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward
          (fiberMap f 0 (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
              z.1).val.subschemeι)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle
            (fiber ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
                z.1).val.subschemeι ≫ f) 0)) :=
  arbitraryFiniteFlatCurve f 0

/-- The literal one endpoint retains all branches, including nonreduced branches. -/
theorem oneEndpoint :
    let := _root_.AlgebraicGeometry.Scheme.IntegralCycle.genericPointFintype P
    _root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber f (1 : k)) =
      ∑ z : genericPoints P, (_root_.AlgebraicGeometry.Scheme.genericMultiplicity z : ℤ) •
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward
          (fiberMap f 1 (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
              z.1).val.subschemeι)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle
            (fiber ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
                z.1).val.subschemeι ≫ f) 1)) :=
  arbitraryFiniteFlatCurve f 1

/-- Actual finite pushforward and arbitrary signed multiples preserve the full equality. -/
theorem signedFinitePushforward (a : k) {Q : Scheme.{u}}
    (g : fiber f a ⟶ Q) [IsFinite g] (n : ℤ) :
    let := _root_.AlgebraicGeometry.Scheme.IntegralCycle.genericPointFintype P
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward g (n •
        _root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber f a)) =
      ∑ z : genericPoints P, (n * (_root_.AlgebraicGeometry.Scheme.genericMultiplicity z : ℤ)) •
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward
          (fiberMap f a (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
              z.1).val.subschemeι ≫ g)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle
            (fiber ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
                z.1).val.subschemeι ≫ f) a)) := by
  classical
  let := _root_.AlgebraicGeometry.Scheme.IntegralCycle.genericPointFintype P
  rw [arbitraryFiniteFlatCurve f a, Finset.smul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [smul_smul, map_zsmul, _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward_comp,
    AddMonoidHom.comp_apply]

open Lean in
run_cmd do
  for name in #[
      ``AlgebraicGeometry.fundamentalCycle_eq_sum_closed_components,
      ``AlgebraicGeometry.closedImmersion_fundamentalCoefficient_eq_length_of_all_generic,
      ``endpoint_ideal, ``endpoint_stalk, ``endpointScalar_regular,
      ``fiberInclusion_stalk, ``scalar_regular, ``fiber_all_generic,
      ``scalar_cut_isArtinian, ``scalar_mem_maximalIdeal,
      ``fiberMap_isPullback, ``fiberMap_composite_stalk,
      ``fundamentalCycle_specialization_of_quotient_regular,
      ``AlgebraicGeometry.finiteFlatCurve_fundamentalCycle_specialization,
      ``arbitraryFiniteFlatCurve, ``zeroEndpoint, ``oneEndpoint, ``signedFinitePushforward] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual finite-flat curve specialization uses only standard foundations."

end MotivicTest.FiniteFlatCurveSpecialization
