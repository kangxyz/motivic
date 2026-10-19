/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.CurveFamily

/-!
# Consumers of whole finite-flat curve correspondences

The field and smooth target are arbitrary. The original finite schemes retain
all components and nilpotents, including at the literal zero and one fibers.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField _root_.Motivic.FiniteFlatCurveFamily
open scoped Polynomial

universe u

namespace MotivicTest.FiniteFlatCurveFamily
open _root_.AlgebraicGeometry.Scheme (IntegralCycle SmoothSite)
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField

variable {k : Type u} [Field k] {Y : SmoothSite (Spec (.of k))}

/-- The smooth-site evaluation has the literal polynomial-evaluation spectrum map. -/
theorem literalEvaluation (a : k) :
    (evaluationPoint k a).left = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) :=
  rfl

/-- A full finite field-point scheme keeps all original local multiplicities. -/
theorem wholePointCycle {P : Scheme.{u}} [IsNoetherian P]
    (f : P ⟶ Spec (.of k)) [IsFinite f]
    (j : P ⟶ pullback (point k).hom Y.hom) [IsClosedImmersion j]
    (hj : j ≫ pullback.fst (point k).hom Y.hom = f) :
    FiniteCorrespondence.toIntegralCycle (f := (point k).hom) (g := Y.hom)
      (pointFundamentalCorrespondence f j hj) =
        IntegralCycle.finitePushforward j (_root_.AlgebraicGeometry.Scheme.fundamentalCycle P) :=
  toIntegralCycle_pointFundamentalCorrespondence f j hj

section Curve

variable {P : Scheme.{u}} [IsNoetherian P]
  (f : P ⟶ Spec (.of k[X])) [IsFinite f] [Flat f]
  (j : P ⟶ ambient Y) [IsClosedImmersion j]
  (hj : j ≫ pullback.fst (line k).hom Y.hom = f)

/-- The actual correspondence forgets to the entire original family cycle. -/
theorem wholeCurveCycle :
    FiniteCorrespondence.toIntegralCycle (f := (line k).hom) (g := Y.hom)
      (fundamentalCorrespondence f j hj) =
        IntegralCycle.finitePushforward j (_root_.AlgebraicGeometry.Scheme.fundamentalCycle P) :=
  toIntegralCycle_fundamentalCorrespondence f j hj

/-- Every actual graph restriction retains the full scheme-theoretic fiber. -/
theorem wholeGraphRestriction (a : k) :
    FiniteCorrespondence.toIntegralCycle (f := (point k).hom) (g := Y.hom)
      ((Cor.graphFunctor k).map (evaluationPoint k a) ≫ fundamentalCorrespondence f j hj) =
        IntegralCycle.finitePushforward (fiberInclusion f j hj a)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber f a)) :=
  toIntegralCycle_graph_restriction f j hj a

/-- The zero endpoint uses the complete original special fiber. -/
theorem zeroGraphRestriction :
    FiniteCorrespondence.toIntegralCycle (f := (point k).hom) (g := Y.hom)
      ((Cor.graphFunctor k).map (evaluationPoint k 0) ≫ fundamentalCorrespondence f j hj) =
        IntegralCycle.finitePushforward (fiberInclusion f j hj 0)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber f 0)) :=
  wholeGraphRestriction f j hj 0

/-- The one endpoint likewise retains every component and its original length. -/
theorem oneGraphRestriction :
    FiniteCorrespondence.toIntegralCycle (f := (point k).hom) (g := Y.hom)
      ((Cor.graphFunctor k).map (evaluationPoint k 1) ≫ fundamentalCorrespondence f j hj) =
        IntegralCycle.finitePushforward (fiberInclusion f j hj 1)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber f 1)) :=
  wholeGraphRestriction f j hj 1

end Curve

open Lean in
run_cmd do
  for name in #[``_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.evaluationPoint,
      ``_root_.Motivic.FiniteFlatCurveFamily.genericComponentGenerator,
          ``_root_.Motivic.FiniteFlatCurveFamily.genericFundamentalCorrespondence,
      ``_root_.Motivic.FiniteFlatCurveFamily.toIntegralCycle_genericFundamentalCorrespondence,
      ``pointFundamentalCorrespondence, ``toIntegralCycle_pointFundamentalCorrespondence,
      ``fundamentalCorrespondence, ``toIntegralCycle_fundamentalCorrespondence,
      ``fiberInclusion_closed, ``componentGenerator_flat,
      ``componentFiberIso_hom_inclusion, ``component_graph_restriction,
      ``toIntegralCycle_graph_restriction,
      ``literalEvaluation, ``wholePointCycle, ``wholeCurveCycle,
      ``wholeGraphRestriction, ``zeroGraphRestriction, ``oneGraphRestriction] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole finite-flat curve correspondences use only standard foundations."

end MotivicTest.FiniteFlatCurveFamily
