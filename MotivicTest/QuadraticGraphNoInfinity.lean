/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.QuadraticGraphNoInfinity
public import Lean

/-! # The original graph and its whole scheme-theoretic boundary -/
public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open QuadraticIncidence QuadraticIncidence.InfinityChart
universe u
namespace MotivicTest.QuadraticGraphNoInfinity

/-- No equation, chart-compatibility, or replacement-closure premise is supplied. -/
theorem original_graph_no_boundary (k R : Type u) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [IsNoetherianRing R] {σ : Type u} [Fintype σ] (g : σ → R)
    (d : ℕ) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (c : Fin (d + 1) × Exponent σ → k) (hc : NoCommonInfinityZero k R g d c)
    (x : (quadraticOriginalGraph k R g d c).image) :
    ((quadraticOriginalGraph k R g d c).imageι ≫ pullback.fst _ _) x ∈
      Set.range (quadraticOriginalToImage k R g) :=
  quadraticOriginalGraph_no_infinity k R g d hg c hc x

/-- A literal equation vanishes on the full schematic image, even for nonreduced rings. -/
theorem nonreduced_equation_transport (A B : Type u) [CommRing A] [CommRing B]
    (φ : A →+* B) (z : A) (hz : φ z = 0) :
    (Spec.map (CommRingCat.ofHom φ)).imageι.appTop ((Scheme.ΓSpecIso (.of A)).inv z) = 0 :=
  Scheme.affineImage_equation_zero φ z hz

open Lean in
run_cmd do
  for name in #[``original_graph_no_boundary, ``nonreduced_equation_transport,
      ``chartGraphEquation_mem_ker, ``chartGraphImage_equation_zero,
      ``chartGraphImage_infinity_isUnit, ``Scheme.polynomialBaseChange_isPullback,
      ``quadraticOriginalGraph_ker, ``quadraticGraphImageChartIso,
      ``quadraticOriginalGraph_no_infinity] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original graph, native polynomial chart, full schematic equation and boundary: audited."

end MotivicTest.QuadraticGraphNoInfinity
