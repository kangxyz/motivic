/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Endpoints

public import Motivic.AlgebraicGeometry.Correspondences.Graph.Components.Pullback
public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.Relative.IncidenceCycle

/-!
# Actual relative endpoint composition on each correspondence generator

The integral right support selects one component of the disconnected smooth
source. Its graph-component incidence is the whole scheme-theoretic endpoint
pullback, and all other graph components contribute zero. The original Tor
composition is therefore the finite pushforward of that whole fiber's
fundamental cycle. The right support projection need not be flat.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
open _root_.Motivic
open _root_.AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) (a : k)

local instance : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)
local instance : IsReduced ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsReduced X.left)

variable (G : _root_.Motivic.FiniteCorrespondenceGenerator (relativeLineHom X.hom) Y.hom)

/-- The surviving graph component gives the full endpoint pullback cycle. -/
theorem component_toIntegralCycle_whole_endpoint
    (E : Set X.left) (hE : E ∈ irreducibleComponents X.left)
    (hG : Set.range (G.projection ≫
      pullback.fst X.hom (AffineLineField.line k).hom) ⊆ E) :
    _root_.Motivic.FiniteCorrespondence.toIntegralCycle
      ((endpointComponentGenerator X a E hE).incidenceTorCorrespondence k
        (X := X) (Y := relativeLineSite X) (Z := Y) G) =
      IntegralCycle.finitePushforward
        (G.graphPullbackMap (endpoint X.hom a) (endpoint_base X.hom a))
        (fundamentalCycle (G.graphPullback (endpoint X.hom a))) := by
  have : IsIso (G.componentGraphPullbackMap (X := X) (Y := relativeLineSite X) (Z := Y)
      (endpoint X.hom a) (endpoint_base X.hom a) E hE) :=
    G.componentGraphPullbackMap_isIso (X := X) (Y := relativeLineSite X) (Z := Y)
      (endpoint X.hom a) (endpoint_base X.hom a) E hE
      (pullback.fst X.hom (AffineLineField.line k).hom) (endpoint_fst X.hom a) hG
  rw [component_toIntegralCycle_incidenceTorCorrespondence]
  simp only [← G.componentGraphPullbackMap_incidenceMap
      (X := X) (Y := relativeLineSite X) (Z := Y)
      (endpoint X.hom a) (endpoint_base X.hom a) E hE,
    IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_fundamentalCycle]
  rfl

/-- The actual graph functor, summed over every source component, restricts a
generator to the whole endpoint fiber with all original local multiplicities. -/
theorem toIntegralCycle_graph_endpoint_generator :
    _root_.Motivic.FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)
      ((_root_.Motivic.Cor.graphFunctor k).map (endpointMorphism X a) ≫
        (show _root_.Motivic.Cor.mk (relativeLineSite X) ⟶ _root_.Motivic.Cor.mk Y from G.cycle)) =
      IntegralCycle.finitePushforward
        (G.graphPullbackMap (endpoint X.hom a) (endpoint_base X.hom a))
        (fundamentalCycle (G.graphPullback (endpoint X.hom a))) := by
  classical
  obtain ⟨E, hE, hG⟩ := G.exists_sourceComponent_of_integral (X := X)
    (Y := relativeLineSite X) (Z := Y)
    (pullback.fst X.hom (AffineLineField.line k).hom)
  change _root_.Motivic.FiniteCorrespondence.toIntegralCycle
    ((_root_.Motivic.FiniteCorrespondence.incidenceTorPairing k
      (X := X) (Y := relativeLineSite X) (Z := Y)).flip G.cycle
        (componentGraphCycleOver (X := X.left) (Y := (relativeLineSite X).left)
          (endpoint X.hom a) (endpoint_base X.hom a))) = _
  rw [componentGraphCycleOver_eq_sum, map_sum, map_sum]
  rw [Finset.sum_eq_single E]
  · rw [dite_eq_left hE]
    change _root_.Motivic.FiniteCorrespondence.toIntegralCycle
      (_root_.Motivic.FiniteCorrespondence.incidenceTorPairing k
        (X := X) (Y := relativeLineSite X) (Z := Y)
        (endpointComponentGenerator X a E hE).cycle G.cycle) = _
    rw [_root_.Motivic.FiniteCorrespondence.incidenceTorPairing_cycle]
    exact component_toIntegralCycle_whole_endpoint X Y a G E hE hG
  · intro D hD hDE
    have hD' : D ∈ irreducibleComponents X.left := by simpa using hD
    rw [dite_eq_left hD']
    change _root_.Motivic.FiniteCorrespondence.toIntegralCycle
      (_root_.Motivic.FiniteCorrespondence.incidenceTorPairing k
        (X := X) (Y := relativeLineSite X) (Z := Y)
        (endpointComponentGenerator X a D hD').cycle G.cycle) = 0
    rw [_root_.Motivic.FiniteCorrespondence.incidenceTorPairing_cycle]
    have : IsEmpty ((componentGraphGeneratorOver (X := X.left)
        (Y := (relativeLineSite X).left) (endpoint X.hom a) (endpoint_base X.hom a)
        D hD').incidence G) :=
      G.componentGraph_incidence_isEmpty_of_ne (X := X) (Y := relativeLineSite X) (Z := Y)
        (endpoint X.hom a) (endpoint_base X.hom a) D hD'
        (pullback.fst X.hom (AffineLineField.line k).hom) (endpoint_fst X.hom a)
        E hE hG hDE
    have hzero :=
        @_root_.Motivic.FiniteCorrespondenceGenerator.incidenceTorCorrespondence_eq_zero_of_isEmpty
      k _ X (relativeLineSite X) (endpointComponentGenerator X a D hD') Y G this
    exact (congrArg _root_.Motivic.FiniteCorrespondence.toIntegralCycle hzero).trans (map_zero _)
  · intro hnot
    exact (hnot (by simpa using hE)).elim

end AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
