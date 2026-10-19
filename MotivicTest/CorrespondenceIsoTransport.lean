/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Graph.IsoTransport

/-!
# Consumers of actual correspondence transport by scheme isomorphisms
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.CorrespondenceIsoTransport
open _root_.AlgebraicGeometry.Scheme (IntegralCycle SmoothSite)

variable (k : Type u) [Field k] {X X' Y Y' : SmoothSite (Spec (.of k))}
  (e : X ≅ X') (d : Y ≅ Y') [IsIntegral X'.left]

/-- Arbitrary signed cycles use the original correspondence composition and
both actual graph maps, without flatness assumptions on their support projections. -/
theorem signedGraphTransport (α : Cor.mk X ⟶ Cor.mk Y) :
    FiniteCorrespondence.toIntegralCycle (f := X'.hom) (g := Y'.hom)
      ((Cor.graphFunctor k).map e.inv ≫ α ≫ (Cor.graphFunctor k).map d.hom) =
      IntegralCycle.finitePushforward (Cor.graphTransportIso k e d).hom
        (FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom) α) :=
  Cor.toIntegralCycle_graphIso_transport k e d α

open Lean in
run_cmd do
  for name in [``Cor.graphTransportIso, ``Cor.graphTransportIso_hom_fst,
      ``Cor.graphTransportIso_hom_snd,
      ``FiniteCorrespondenceGenerator.toIntegralCycle_graphIso_comp_cycle,
      ``FiniteCorrespondenceGenerator.graphPullbackMap_iso_eq,
      ``FiniteCorrespondenceGenerator.toIntegralCycle_graphIso_comp_cycle_pushforward,
      ``Cor.toIntegralCycle_graphIso_comp, ``Cor.toIntegralCycle_graphIso_transport,
      ``signedGraphTransport] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual graph transport uses only standard foundations."

end MotivicTest.CorrespondenceIsoTransport
