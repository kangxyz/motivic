/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Basic
public import Motivic.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.CurveFamily

/-!
# Whole affine-line endpoint compatibility for finite-flat spans

The finite-flat span producer agrees with the existing finite-flat curve
family producer when the joint source-target map is a closed immersion.
The proved whole-fibre specialization theorem then identifies graph
precomposition with the actual endpoint span, including every nilpotent and
local multiplicity. No new intersection or deformation engine is introduced.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial

universe u

namespace Motivic.Cor
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k] {Y : SmoothSite (Spec (.of k))}
  {D : Scheme.{u}} (f : D ⟶ Spec (.of k[X]))
  [IsFinite f] [Flat f] (g : D ⟶ Y.left)
  (h : f ≫ (AffineLineField.line k).hom = g ≫ Y.hom)

/-- The whole endpoint is the canonical scheme-theoretic pullback. -/
abbrev finiteFlatSpanFiber (a : k) : Scheme.{u} := FiniteFlatCurve.fiber f a

include h in
omit [IsFinite f] [Flat f] in
/-- The two original endpoint coordinates satisfy the same base equation. -/
theorem finiteFlatSpanFiber_base (a : k) :
    pullback.fst (FiniteFlatCurve.endpoint a) f ≫ (AffineLineField.point k).hom =
      (pullback.snd (FiniteFlatCurve.endpoint a) f ≫ g) ≫ Y.hom := by
  rw [Category.assoc, ← h, ← Category.assoc, ← pullback.condition, Category.assoc]
  exact congrArg (fun q ↦ pullback.fst (FiniteFlatCurve.endpoint a) f ≫ q)
    (MorphismProperty.Over.w (AffineLineField.evaluationPoint k a)).symm

/-- The actual span of the entire endpoint fibre, without reducing its scheme. -/
def finiteFlatSpanEndpoint (a : k) :
    Cor.mk (AffineLineField.point k) ⟶ Cor.mk Y :=
  ofFiniteFlatSpan (X := AffineLineField.point k) (Y := Y)
    (pullback.fst (FiniteFlatCurve.endpoint a) f)
    (pullback.snd (FiniteFlatCurve.endpoint a) f ≫ g) (finiteFlatSpanFiber_base f g h a)

variable [IsClosedImmersion (pullback.lift f g h)]

/-- The general finite-flat span and the existing embedded curve-family
producer have exactly the same original fundamental-cycle pushforward. -/
theorem ofFiniteFlatSpan_eq_curveFundamental :
    ofFiniteFlatSpan (X := AffineLineField.line k) (Y := Y) f g h =
      letI : IsNoetherian D := isNoetherian_of_finiteType f
      FiniteFlatCurveFamily.fundamentalCorrespondence (Y := Y) f (pullback.lift f g h)
        (pullback.lift_fst _ _ _) := by
  have : IsNoetherian D := isNoetherian_of_finiteType f
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_ofFiniteFlatSpan,
    FiniteFlatCurveFamily.toIntegralCycle_fundamentalCorrespondence]

/-- Graph evaluation of the finite-flat span is the entire endpoint span.
The closed joint-map hypothesis is explicit; flatness is imposed on the
family, never on the closed evaluation morphism. -/
theorem graph_evaluation_ofFiniteFlatSpan (a : k) :
    (Cor.graphFunctor k).map (AffineLineField.evaluationPoint k a) ≫
        ofFiniteFlatSpan (X := AffineLineField.line k) (Y := Y) f g h =
      finiteFlatSpanEndpoint f g h a := by
  have : IsNoetherian D := isNoetherian_of_finiteType f
  rw [ofFiniteFlatSpan_eq_curveFundamental]
  apply FiniteCorrespondence.toIntegralCycle_injective
  refine (FiniteFlatCurveFamily.toIntegralCycle_graph_restriction (Y := Y) f
    (pullback.lift f g h) (pullback.lift_fst _ _ _) a).trans ?_
  rw [finiteFlatSpanEndpoint, toIntegralCycle_ofFiniteFlatSpan]
  congr 2
  apply pullback.hom_ext
  · simp only [FiniteFlatCurveFamily.fiberInclusion_fst]
    exact (pullback.lift_fst _ _ _).symm
  · simp only [FiniteFlatCurveFamily.fiberInclusion_snd, pullback.lift_snd]
    exact (pullback.lift_snd _ _ _).symm

end Motivic.Cor
