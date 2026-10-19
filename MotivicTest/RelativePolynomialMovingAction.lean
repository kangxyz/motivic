/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.Moving.PolynomialRelative
public import Lean
/-! # Relative moving acts in the original k-correspondence category -/
public noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial Motivic
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
universe v u
namespace MotivicTest.RelativePolynomialMovingAction

/-- No new base-field presheaf or sheaf condition is introduced. -/
theorem actual_relative_moving (k R A : Type u) [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra.Smooth k R] [Algebra R A] [Algebra k A]
    [IsScalarTower k R A] [Algebra.Smooth k A] [IsDomain A] [IsNoetherianRing A]
    (f g : R[X]) (hf : f.Monic) (hg : g.Monic) (hfg : IsCoprime f g)
    (a : A) (ha : IsUnit ((f.map (algebraMap R A)).eval a))
    (j : sourceSite (k := k) (A := A) ⟶ openSite (k := k) f)
    (hj : j ≫ openInclusion (k := k) f = coordinateMorphism (k := k) (R := R) a) :
    ∃ β : Cor.mk (sourceSite (k := k) (A := A)) ⟶ Cor.mk (openSite (k := k) (f * g)),
      ∀ (P : PresheafWithTransfers.{v} k), P.IsA1Invariant →
        P.transfer ((Cor.graphFunctor k).map j) =
          P.transfer ((Cor.graphFunctor k).map (narrowInclusion (k := k) f g)) ≫
            P.transfer β :=
  exists_moving_action f g hf hg hfg a ha j hj

open Lean in
run_cmd do
  for name in #[``actual_relative_moving,
      ``_root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite.exists_moving_action,
      ``_root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite.graph_familyCycle,
          ``_root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite.cycle_mul,
          ``_root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite.cycle_linear_graph] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Relative moving in the original k-correspondence category: standard foundations only."

end MotivicTest.RelativePolynomialMovingAction
