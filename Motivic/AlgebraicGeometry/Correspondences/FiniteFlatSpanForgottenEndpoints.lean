/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.FiniteFlatSpanEndpoints
public import Motivic.AlgebraicGeometry.Correspondences.FiniteFlatSpanGraph

/-!
# Whole endpoints after forgetting a retained coordinate

A closed retained parameter/target map permits whole-fibre specialization.
An arbitrary map from that smooth target can then forget the coordinate:
the resulting family and endpoint are the direct original finite-flat spans,
with no closedness or finiteness assumption on the forgotten target map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial

universe u

namespace Motivic.Cor

variable {k : Type u} [Field k] {Y Z : SmoothSite (Spec (.of k))}
  {D : Scheme.{u}} (f : D ⟶ Spec (.of k[X])) [IsFinite f] [Flat f]
  (g : D ⟶ Y.left) (h : f ≫ (FiniteFlatCurveFamily.line k).hom = g ≫ Y.hom)
  (q : Y ⟶ Z)

/-- Forgetting a target coordinate commutes with taking the actual whole endpoint
span, even if different components then have the same target image. -/
theorem finiteFlatSpanEndpoint_comp_graph (a : k) :
    finiteFlatSpanEndpoint f g h a ≫ (graphFunctor k).map q =
      finiteFlatSpanEndpoint f (g ≫ q.left)
        (finiteFlatSpan_postcompose_base (X := FiniteFlatCurveFamily.line k) f g h q) a := by
  simpa only [finiteFlatSpanEndpoint, Category.assoc] using
    ofFiniteFlatSpan_comp_graph (X := FiniteFlatCurveFamily.point k) (Y := Y) (Z := Z)
      (pullback.fst (FiniteFlatCurve.endpoint a) f)
      (pullback.snd (FiniteFlatCurve.endpoint a) f ≫ g)
      (finiteFlatSpanFiber_base f g h a) q

variable [IsClosedImmersion (pullback.lift f g h)]

/-- Whole-fibre evaluation survives any forgetting map from a retained smooth
target. Only the retained joint map is assumed closed; both displayed spans use
the final target and the original source schemes directly. -/
theorem graph_evaluation_ofFiniteFlatSpan_postcompose (a : k) :
    (graphFunctor k).map (FiniteFlatCurveFamily.evaluationPoint k a) ≫
        ofFiniteFlatSpan (X := FiniteFlatCurveFamily.line k) (Y := Z) f (g ≫ q.left)
          (finiteFlatSpan_postcompose_base (X := FiniteFlatCurveFamily.line k) f g h q) =
      finiteFlatSpanEndpoint f (g ≫ q.left)
        (finiteFlatSpan_postcompose_base (X := FiniteFlatCurveFamily.line k) f g h q) a := by
  rw [← ofFiniteFlatSpan_comp_graph (X := FiniteFlatCurveFamily.line k) f g h q, ← Category.assoc,
    graph_evaluation_ofFiniteFlatSpan f g h,
    finiteFlatSpanEndpoint_comp_graph f g h q]

end Motivic.Cor
