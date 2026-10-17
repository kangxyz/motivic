/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.NisnevichCechGraphPushforward
public import Lean.Util.CollectAxioms

/-!
# Actual Tor coefficients survive graph postcomposition

The consumer uses the complete incidence Tor coefficient function and a
literal postcomposed support map. The graph arrow need not be finite or étale.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.FiniteCorrespondenceGenerator

universe u

namespace MotivicTest.NisnevichCechGraphPushforward

example {k : Type u} [Field k] {T X Y V : SmoothSite (Spec (.of k))}
    (G : FiniteCorrespondenceGenerator T.hom X.hom)
    (A : FiniteCorrespondenceGenerator X.hom V.hom)
    (q : V ⟶ Y) (j : G.incidence A ⟶ pullback T.hom Y.hom) [IsFinite j]
    (hj₁ : j ≫ pullback.fst T.hom Y.hom = G.incidenceSource A)
    (hj₂ : j ≫ pullback.snd T.hom Y.hom = G.incidenceTarget A ≫ q.left) :
    FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := Y.hom)
      ((G.incidenceTorCorrespondence k A : Cor.mk T ⟶ Cor.mk V) ≫
        (Cor.graphFunctor k).map q) =
      IntegralCycle.finitePushforward j (IntegralCycle.ofGenericCoefficients (G.incidence A)
        (G.incidenceTorCoefficient (S := Spec (.of k)) A)) :=
  toIntegralCycle_graph_incidenceTor k G A q j hj₁ hj₂

open Lean in
run_cmd do
  for name in #[``toIntegralCycle_graph_of_generic_coefficients,
      ``toIntegralCycle_graph_incidenceTor] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.NisnevichCechGraphPushforward
