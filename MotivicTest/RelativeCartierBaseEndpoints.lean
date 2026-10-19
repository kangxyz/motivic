/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.Cartier.BaseEndpoints
public import MotivicTest.RelativeFiniteFlatSpanEndpoints

/-!
# Relative Cartier endpoints with no target embedding premise

The source is the actual disconnected smooth two-line scheme. Only the
original separated finite-type relative curve, its proper flat Cartier
divisor, the actual boundary-avoiding open, and an arbitrary target map are
supplied. The finite-flat family and retained joint embedding are derived.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules.Invertible Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
open MotivicTest.FlatPolynomialComponentRegularity

namespace MotivicTest.RelativeCartierBaseEndpoints

variable {Y : SmoothSite (Spec (.of ℚ))} {C D U : Scheme}
  (p : C ⟶ relativeLine twoLines.hom) [SmoothOfRelativeDimension 1 p]
  [IsSeparated p] [QuasiCompact p] (i : D ⟶ C) [IsClosedImmersion i]
  (hI : IsLocallyRankOne C (idealModule i)) [Flat (i ≫ p)] [IsProper (i ≫ p)]
  (j : U ⟶ C) [IsOpenImmersion j] (hAvoid : Set.range i ⊆ Set.range j)
  (g : U ⟶ Y.left) (hbase : j ≫ p ≫ relativeLineHom twoLines.hom = g ≫ Y.hom)

/-- The actual arbitrary-target Cartier correspondence has the whole relative endpoint. -/
theorem arbitrary_target_relative_cartier (a : ℚ) :
    (Cor.graphFunctor ℚ).map (endpointMorphism twoLines a) ≫
        RelativeCartierDivisor.correspondence (X := relativeLineSite twoLines) (Y := Y)
          p i hI j hAvoid g hbase =
      RelativeCartierDivisor.relativeEndpointCorrespondence twoLines
        p j i hI hAvoid g hbase a :=
  RelativeCartierDivisor.graph_relative_endpoint_correspondence twoLines
    p j i hI hAvoid g hbase a

example := arbitrary_target_relative_cartier p i hI j hAvoid g hbase 0

example := arbitrary_target_relative_cartier p i hI j hAvoid g hbase 1

open Lean in
run_cmd do
  for name in #[``arbitrary_target_relative_cartier,
      ``RelativeCartierDivisor.relativeRetainedOpen,
      ``RelativeCartierDivisor.graph_relative_endpoint_correspondence] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {name}"

end MotivicTest.RelativeCartierBaseEndpoints
