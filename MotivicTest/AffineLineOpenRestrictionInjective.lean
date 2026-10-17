/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.AffineLineOpenRestrictionInjective
public import Lean
/-! # Original affine-line restriction, with no sheaf or infinite-field assumption -/
public noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial
open Motivic Motivic.PolynomialOpenSpans Motivic.AffineLineReducedComplement
universe v u
namespace MotivicTest.AffineLineOpenRestrictionInjective

/-- The unchanged original opens and original graph are the theorem's endpoints. -/
theorem actual_original_restriction (k : Type u) [Field k]
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (U V : (line k).Opens) (hVU : V ≤ U) (hV : (V : Set (line k)).Nonempty) :
    Function.Injective (P.transfer ((Cor.graphFunctor k).map
      (originalOpenInclusion U V hVU))) :=
  original_open_restriction_injective P hP U V hVU hV

/-- A section locally zero on a nonempty open is actually zero, before sheafification. -/
theorem actual_section_zero (k : Type u) [Field k]
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (U V : (line k).Opens) (hVU : V ≤ U) (hV : (V : Set (line k)).Nonempty)
    (s : P.sections (Cor.mk (openObject U)))
    (hs : P.transfer ((Cor.graphFunctor k).map (originalOpenInclusion U V hVU)) s = 0) :
    s = 0 := by
  apply actual_original_restriction k P hP U V hVU hV
  exact hs.trans (map_zero (P.transfer ((Cor.graphFunctor k).map
    (originalOpenInclusion U V hVU))).hom).symm

open Lean in
run_cmd do
  for name in #[``actual_original_restriction, ``actual_section_zero,
      ``original_open_restriction_injective, ``exists_moving_action,
      ``transfer_cycle_eq_of_boundary_one, ``graph_familyCycle,
      ``cycle_mul, ``cycle_linear_graph] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original restriction and signed moving action: standard foundations only."

end MotivicTest.AffineLineOpenRestrictionInjective
