/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.Cartier.ArbitraryTargetEndpoints
public import MotivicTest.FiniteFlatSpanEndpoints

/-!
# Endpoints with an actually nonfinite coordinate-forgetting map

The affine-line structure map is proved nonfinite. Forgetting the root of the
two-double-section family nevertheless preserves the exact endpoint span; the
source is the same nonreduced disconnected quotient tested in the first cohort.
The Cartier consumer has no joint-map or target-map embedding assumption.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic Polynomial
open AlgebraicGeometry.FiniteTwoUnitPolynomialFamily
open MotivicTest.FiniteFlatSpanEndpoints

universe u

namespace MotivicTest.FiniteFlatSpanForgottenEndpoints
open _root_.AlgebraicGeometry.Scheme.SmoothSite

/-- Forget the entire affine root coordinate. -/
def forgetRoot (k : Type u) [Field k] :
    AffineLineField.line k ⟶ AffineLineField.point k :=
  SmoothSite.homMk (AffineLineField.line k).hom (Category.comp_id _)

/-- This consumer genuinely uses an ambient target map which is not finite. -/
theorem forgetRoot_not_finite (k : Type u) [Field k] : ¬ IsFinite (forgetRoot k).left := by
  change ¬ IsFinite (Spec.map (CommRingCat.ofHom (C : k →+* k[X])))
  intro h
  have hf := (IsFinite.SpecMap_iff (CommRingCat.ofHom (C : k →+* k[X]))).mp h
  exact Polynomial.not_finite (RingHom.finite_algebraMap.mp hf)

/-- Both original double components can have the same final target image.
The actual graph-evaluated correspondence is still the full endpoint span. -/
theorem twoDoubleSections_forgottenEndpoint (a : ℚ) :
    letI : IsFinite (projection twoDoubleSections) := projection_finite twoDoubleSections_monic
    letI : Flat (projection twoDoubleSections) := projection_flat twoDoubleSections_monic
    (Cor.graphFunctor ℚ).map (AffineLineField.evaluationPoint ℚ a) ≫
        Cor.ofFiniteFlatSpan (X := AffineLineField.line ℚ)
          (Y := AffineLineField.point ℚ) (projection twoDoubleSections)
          (rootMap twoDoubleSections ≫ (forgetRoot ℚ).left)
          (Cor.finiteFlatSpan_postcompose_base (X := AffineLineField.line ℚ)
            (Y := AffineLineField.line ℚ) (Z := AffineLineField.point ℚ)
            (projection twoDoubleSections) (rootMap twoDoubleSections)
            (rootSpanBase twoDoubleSections) (forgetRoot ℚ)) =
      Cor.finiteFlatSpanEndpoint (Y := AffineLineField.point ℚ)
        (projection twoDoubleSections) (rootMap twoDoubleSections ≫ (forgetRoot ℚ).left)
        (Cor.finiteFlatSpan_postcompose_base (X := AffineLineField.line ℚ)
            (Y := AffineLineField.line ℚ) (Z := AffineLineField.point ℚ)
          (projection twoDoubleSections) (rootMap twoDoubleSections)
          (rootSpanBase twoDoubleSections) (forgetRoot ℚ)) a := by
  have : IsFinite (projection twoDoubleSections) := projection_finite twoDoubleSections_monic
  have : Flat (projection twoDoubleSections) := projection_flat twoDoubleSections_monic
  have : IsClosedImmersion (pullback.lift (projection twoDoubleSections)
      (rootMap twoDoubleSections) (rootSpanBase twoDoubleSections)) :=
    rootSpanClosed twoDoubleSections twoDoubleSections_monic
  exact Cor.graph_evaluation_ofFiniteFlatSpan_postcompose
    (Y := AffineLineField.line ℚ) (Z := AffineLineField.point ℚ)
    (projection twoDoubleSections) (rootMap twoDoubleSections)
    (rootSpanBase twoDoubleSections) (forgetRoot ℚ) a

section Cartier

open Scheme.Modules.Invertible Scheme.Hom

variable {k : Type u} [Field k] {Y : SmoothSite (Spec (.of k))}
  {C D U : Scheme.{u}} (p : C ⟶ Spec (.of k[X]))
  [SmoothOfRelativeDimension 1 p] [IsSeparated p] [QuasiCompact p]
  (i : D ⟶ C) [IsClosedImmersion i] (hI : IsLocallyRankOne C (idealModule i))
  [Flat (i ≫ p)] [IsProper (i ≫ p)]
  (j : U ⟶ C) [IsOpenImmersion j] (hAvoid : Set.range i ⊆ Set.range j)
  (g : U ⟶ Y.left)
  (hbase : j ≫ p ≫ (AffineLineField.line k).hom = g ≫ Y.hom)

/-- Arbitrary-target standard-curve consumer: no embedding condition is supplied. -/
theorem arbitraryTargetCartierEndpoint (a : k) :
    (Cor.graphFunctor k).map (AffineLineField.evaluationPoint k a) ≫
        RelativeCartierDivisor.correspondence (X := AffineLineField.line k)
          (Y := Y) p i hI j hAvoid g hbase =
      RelativeCartierDivisor.endpointCorrespondence p i hI j hAvoid g hbase a :=
  RelativeCartierDivisor.graph_evaluation_correspondence_of_separated_quasiCompact
    p j i hI hAvoid g hbase a

end Cartier

open Lean in
run_cmd do
  for name in #[``Cor.toPoints_comp_graph, ``Cor.finiteFlatSpan_postcompose_base,
      ``Cor.ofFiniteFlatSpan_comp_graph, ``Cor.finiteFlatSpanEndpoint_comp_graph,
      ``Cor.graph_evaluation_ofFiniteFlatSpan_postcompose,
      ``RelativeCartierDivisor.retainedOpen,
      ``RelativeCartierDivisor.graph_evaluation_correspondence_of_separated_quasiCompact,
      ``RelativeCartierDivisor.graph_endpoints_correspondence_of_separated_quasiCompact,
      ``forgetRoot_not_finite, ``twoDoubleSections_forgottenEndpoint,
      ``arbitraryTargetCartierEndpoint] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Arbitrary-target whole-fibre endpoints use only standard foundations."

end MotivicTest.FiniteFlatSpanForgottenEndpoints
