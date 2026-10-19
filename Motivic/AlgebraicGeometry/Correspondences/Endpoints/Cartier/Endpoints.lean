/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.Cartier.Divisor
public import Motivic.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Endpoints

/-!
# Actual affine-line endpoints of proper flat Cartier families

The endpoint is the original scheme-theoretic divisor fibre with its full
fundamental-cycle multiplicities. Finiteness is supplied by the proved proper
flat relative Cartier theorem. The joint map into parameter times target is
explicitly required to be a closed immersion, exactly the domain of the
existing finite-flat curve specialization engine.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom
open scoped Polynomial

universe u

namespace Motivic.RelativeCartierDivisor
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k] {Y : SmoothSite (Spec (.of k))}
  {C D U : Scheme.{u}} (p : C ⟶ Spec (.of k[X])) (i : D ⟶ C)
  [SmoothOfRelativeDimension 1 p] [IsClosedImmersion i]
  (hI : IsLocallyRankOne C (idealModule i)) [Flat (i ≫ p)] [IsProper (i ≫ p)]
  (j : U ⟶ C) [IsOpenImmersion j]
  (hAvoid : Set.range i ⊆ Set.range j) (g : U ⟶ Y.left)
  (hbase : j ≫ p ≫ (AffineLineField.line k).hom = g ≫ Y.hom)

/-- The actual full endpoint span of the original Cartier family. Its source
is the canonical pullback by evaluation, without any reduced replacement. -/
def endpointCorrespondence (a : k) :
    Cor.mk (AffineLineField.point k) ⟶ Cor.mk Y := by
  have : IsFinite (i ≫ p) :=
    (isFinite_and_locallyOfFinitePresentation_of_proper_flat_cartier p i hI).1
  exact Cor.finiteFlatSpanEndpoint (i ≫ p) (targetMap i j hAvoid g)
    (targetMap_base (X := AffineLineField.line k) (Y := Y) p i j hAvoid g hbase) a

omit [SmoothOfRelativeDimension 1 p] [Flat (i ≫ p)] [IsProper (i ≫ p)] in
/-- Retaining the ambient open as a closed target supplies the joint embedding.
In particular this applies to the identity map of the retained smooth open;
no injectivity of a later map forgetting that coordinate is asserted. -/
theorem productMap_closed_of_target_closed [IsClosedImmersion g] :
    IsClosedImmersion
      (productMap (X := AffineLineField.line k) (Y := Y) p i j hAvoid g hbase) := by
  have : IsClosedImmersion (IsOpenImmersion.lift j i hAvoid ≫ j) := by
    rw [IsOpenImmersion.lift_fac]
    infer_instance
  have : IsClosedImmersion (IsOpenImmersion.lift j i hAvoid) :=
    IsClosedImmersion.of_comp _ j
  have : IsClosedImmersion (targetMap i j hAvoid g) := by
    dsimp only [targetMap]
    infer_instance
  have : IsClosedImmersion
      (productMap (X := AffineLineField.line k) (Y := Y) p i j hAvoid g hbase ≫
        pullback.snd (AffineLineField.line k).hom Y.hom) := by
    dsimp only [productMap]
    rw [pullback.lift_snd]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd _ _)

variable [IsClosedImmersion
  (productMap (X := AffineLineField.line k) (Y := Y) p i j hAvoid g hbase)]

/-- The actual Cartier correspondence specializes by graph precomposition to
its entire endpoint span. Flatness of the divisor over the parameter remains
an explicit hypothesis; it is not inferred from its absolute Cartier ideal. -/
theorem graph_evaluation_correspondence (a : k) :
    (Cor.graphFunctor k).map (AffineLineField.evaluationPoint k a) ≫
        correspondence (X := AffineLineField.line k) (Y := Y) p i hI j hAvoid g hbase =
      endpointCorrespondence p i hI j hAvoid g hbase a := by
  have : IsFinite (i ≫ p) :=
    (isFinite_and_locallyOfFinitePresentation_of_proper_flat_cartier p i hI).1
  have : IsClosedImmersion (pullback.lift (i ≫ p) (targetMap i j hAvoid g)
      (targetMap_base (X := AffineLineField.line k) (Y := Y) p i j hAvoid g hbase)) :=
    inferInstanceAs (IsClosedImmersion
      (productMap (X := AffineLineField.line k) (Y := Y) p i j hAvoid g hbase))
  exact Cor.graph_evaluation_ofFiniteFlatSpan (i ≫ p) (targetMap i j hAvoid g)
    (targetMap_base (X := AffineLineField.line k) (Y := Y) p i j hAvoid g hbase) a

/-- Both literal affine-line endpoints retain the full original divisor fibres. -/
theorem graph_endpoints_correspondence :
    ((Cor.graphFunctor k).map (AffineLineField.evaluationPoint k 0) ≫
        correspondence (X := AffineLineField.line k) (Y := Y) p i hI j hAvoid g hbase =
      endpointCorrespondence p i hI j hAvoid g hbase 0) ∧
    ((Cor.graphFunctor k).map (AffineLineField.evaluationPoint k 1) ≫
        correspondence (X := AffineLineField.line k) (Y := Y) p i hI j hAvoid g hbase =
      endpointCorrespondence p i hI j hAvoid g hbase 1) :=
  ⟨graph_evaluation_correspondence p i hI j hAvoid g hbase 0,
    graph_evaluation_correspondence p i hI j hAvoid g hbase 1⟩

end Motivic.RelativeCartierDivisor
