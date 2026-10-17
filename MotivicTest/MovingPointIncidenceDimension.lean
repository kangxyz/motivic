/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Motivic.Aglib.RingTheory.Bertini.MovingPointIncidenceDimension
import Lean.Util.CollectAxioms

/-! # Actual prime incidence components have fewer projection parameters -/
noncomputable section
open Module TensorProduct KaehlerDifferential
universe u
namespace QuadraticIncidence.MovingPointChart
variable (k R B : Type u) [Field k] [CommRing R] [IsDomain R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
  [Module.Finite R B] [Algebra.Smooth k R] {σ : Type u} [Fintype σ]

example
    (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (a : σ → B) (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (i₀ : Fin d) (j : σ) (P : Ideal (incidenceRing k R B g a d i₀ j)) [P.IsPrime] :
    Algebra.trdeg k (FractionRing (incidenceRing k R B g a d i₀ j ⧸ P)) + 1 ≤
      (d * Fintype.card (Exponent σ) : ℕ) :=
  trdeg_component_fractionField_add_one_le k R B g hg a d hd i₀ j P

open Lean in
run_cmd do
  for name in #[``selected_ne_moving, ``trdeg_component_fractionField_add_one_le] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual incidence component dimension drop: standard foundations only."

end QuadraticIncidence.MovingPointChart
