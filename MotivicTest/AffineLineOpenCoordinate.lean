/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.AffineLine.Open.AffineLineOpenCoordinate
public import Lean

/-! # Direct original-open coordinate consumers -/
public noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial
open _root_.AlgebraicGeometry.Scheme.AffineLineReducedComplement
universe u
namespace MotivicTest.AffineLineOpenCoordinate
open _root_.AlgebraicGeometry.Scheme.AffineLineReducedComplement
variable {k : Type u} [Field k]

/-- All affine-ring hypotheses come from the original nonempty open and its equation. -/
theorem original_open_coordinate_inputs (U : (line k).Opens)
    (hU : (U : Set (line k)).Nonempty) (f : k[X])
    (hD : PrimeSpectrum.basicOpen f = U) :
    letI := openCoordinateAlgebra U
    IsDomain Γ(U.toScheme, ⊤) ∧ IsNoetherianRing Γ(U.toScheme, ⊤) ∧
      Algebra.Smooth k Γ(U.toScheme, ⊤) ∧
      IsUnit ((f.map (algebraMap k (openCoordinateRing U))).eval (openCoordinate U)) := by
  let := openCoordinateAlgebra U
  let : IsAffine U.toScheme := open_isAffine_of_basicOpen_eq U f hD
  exact ⟨openCoordinateRing_isDomain U hU, openCoordinateRing_noetherian U,
    openCoordinateRing_smooth U, openCoordinate_eval_isUnit U f hD.ge⟩

/-- The actual canonical affine comparison lands by the original open embedding. -/
theorem original_spec_coordinate_map (U : (line k).Opens) (f : k[X])
    (hD : PrimeSpectrum.basicOpen f = U) :
    letI := openCoordinateAlgebra U
    letI : IsAffine U.toScheme := open_isAffine_of_basicOpen_eq U f hD
    Spec.map (CommRingCat.ofHom
      (eval₂RingHom (algebraMap k (openCoordinateRing U)) (openCoordinate U))) =
      U.toScheme.isoSpec.inv ≫ U.ι := by
  let := openCoordinateAlgebra U
  let : IsAffine U.toScheme := open_isAffine_of_basicOpen_eq U f hD
  exact spec_eval_eq_original_inclusion U

open Lean in
run_cmd do
  for name in #[``original_open_coordinate_inputs, ``original_spec_coordinate_map,
      ``openPolynomialRestriction_eq_eval, ``openCoordinate_eval_isUnit] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original open global sections, units and Spec maps: standard foundations only."

end MotivicTest.AffineLineOpenCoordinate
