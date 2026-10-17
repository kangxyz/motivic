/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RelativeEndpointClosedFamily
public import Motivic.AlgebraicGeometry.Correspondences.FiniteFlatSpanGraph

/-!
# Actual relative endpoint compatibility for finite-flat spans

The source is any disconnected smooth scheme `X`. Graph precomposition by the
literal `X → X × A¹` endpoint gives the original finite-flat span's whole
scheme-theoretic endpoint, retaining nilpotents and all local multiplicities.
The embedded version has an explicit joint closed-immersion hypothesis. An
arbitrary map from that retained smooth target can then be forgotten by the
proved graph-postcomposition formula, with no finiteness or embedding condition
on the forgetting map or final joint map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic.RelativeEndpointDiagram

universe u

namespace Motivic.Cor

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  {D : Scheme.{u}} (f : D ⟶ relativeLine X.hom) [IsFinite f] [Flat f]
  (g : D ⟶ Y.left) (h : f ≫ relativeLineHom X.hom = g ≫ Y.hom)

local instance : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

include h in
omit [IsFinite f] [Flat f] in
/-- The two original endpoint coordinates retain their actual base equation. -/
theorem relativeFiniteFlatSpanEndpoint_base (a : k) :
    pullback.fst (endpoint X.hom a) f ≫ X.hom =
      (pullback.snd (endpoint X.hom a) f ≫ g) ≫ Y.hom := by
  rw [Category.assoc, ← h, ← Category.assoc, ← pullback.condition,
    Category.assoc, endpoint_base]

/-- The direct finite-flat span of the entire original relative endpoint. -/
def relativeFiniteFlatSpanEndpoint (a : k) : Cor.mk X ⟶ Cor.mk Y :=
  ofFiniteFlatSpan (X := X) (Y := Y) (pullback.fst (endpoint X.hom a) f)
    (pullback.snd (endpoint X.hom a) f ≫ g) (relativeFiniteFlatSpanEndpoint_base f g h a)

/-- Forgetting any retained smooth target commutes with the direct whole endpoint. -/
theorem relativeFiniteFlatSpanEndpoint_comp_graph (q : Y ⟶ Z) (a : k) :
    relativeFiniteFlatSpanEndpoint f g h a ≫ (graphFunctor k).map q =
      relativeFiniteFlatSpanEndpoint f (g ≫ q.left)
        (finiteFlatSpan_postcompose_base (X := relativeLineSite X) f g h q) a := by
  simpa only [relativeFiniteFlatSpanEndpoint, Category.assoc] using
    ofFiniteFlatSpan_comp_graph (X := X) (Y := Y) (Z := Z)
      (pullback.fst (endpoint X.hom a) f) (pullback.snd (endpoint X.hom a) f ≫ g)
      (relativeFiniteFlatSpanEndpoint_base f g h a) q

variable [IsClosedImmersion (pullback.lift f g h)]

/-- The actual relative endpoint graph gives the entire original endpoint span.
Only the retained joint map is required to be closed. -/
theorem graph_relative_endpoint_ofFiniteFlatSpan (a : k) :
    (graphFunctor k).map (endpointMorphism X a) ≫
        ofFiniteFlatSpan (X := relativeLineSite X) (Y := Y) f g h =
      relativeFiniteFlatSpanEndpoint f g h a := by
  have : IsNoetherian D := relativeFiniteFlat_isNoetherian X f
  apply FiniteCorrespondence.toIntegralCycle_injective
  refine (toIntegralCycle_relative_fundamental_endpoint (X := X) (Y := Y) f
    (pullback.lift f g h) (pullback.lift_fst _ _ _) a).trans ?_
  rw [relativeFiniteFlatSpanEndpoint, toIntegralCycle_ofFiniteFlatSpan]
  congr 2
  apply pullback.hom_ext
  · simp only [relativeFiberSpanMap_fst]
    exact (pullback.lift_fst _ _ _).symm
  · simp only [relativeFiberSpanMap_snd, pullback.lift_snd]
    exact (pullback.lift_snd _ _ _).symm

/-- Endpoint compatibility after an arbitrary actual forgetting map. Both
sides use the final target and the original whole finite-flat source directly. -/
theorem graph_relative_endpoint_ofFiniteFlatSpan_postcompose (q : Y ⟶ Z) (a : k) :
    (graphFunctor k).map (endpointMorphism X a) ≫
        ofFiniteFlatSpan (X := relativeLineSite X) (Y := Z) f (g ≫ q.left)
          (finiteFlatSpan_postcompose_base (X := relativeLineSite X) f g h q) =
      relativeFiniteFlatSpanEndpoint f (g ≫ q.left)
        (finiteFlatSpan_postcompose_base (X := relativeLineSite X) f g h q) a := by
  rw [← ofFiniteFlatSpan_comp_graph (X := relativeLineSite X) f g h q,
    ← Category.assoc, graph_relative_endpoint_ofFiniteFlatSpan,
    relativeFiniteFlatSpanEndpoint_comp_graph]

end Motivic.Cor
