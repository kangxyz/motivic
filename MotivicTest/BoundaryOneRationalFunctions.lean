/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Polynomial.BoundaryOneRationalFunctions.Basic
public import Lean.Util.CollectAxioms

/-! # Direct consumers of actual boundary-one localized rational functions -/

@[expose] public noncomputable section

open Polynomial.BoundaryOneRationalFunctions
open scoped Polynomial

universe u

namespace MotivicTest.BoundaryOneRationalFunctions

variable (R : Type u) [CommRing R]

/-- In particular the coefficient map may be the noninjective zero specialization. -/
def zeroSpecialization : group R[X] →* group R := map (Polynomial.evalRingHom 0)

/-- Noninjective one specialization is available as well. -/
def oneSpecialization : group R[X] →* group R := map (Polynomial.evalRingHom 1)

theorem actual_boundary_one (f : group R) :
    zeroValue R (f.val : Polynomial.BoundaryOneRationalFunctions.Ring R) = 1 :=
  zeroValue_eq_one f

theorem actual_ring_inclusion :
    Function.Injective (algebraMap R[X] (Polynomial.BoundaryOneRationalFunctions.Ring R)) :=
  algebraMap_injective R

theorem identity_specialization (f : group R) : map (RingHom.id R) f = f := map_id f

open Lean in
run_cmd do
  for name in #[``denominators, ``denominators_le_nonZeroDivisors,
      ``algebraMap_injective, ``polynomialUnit, ``fraction, ``fraction_mul,
      ``fraction_inv, ``fraction_eq_iff, ``fraction_eq_one_iff, ``group,
      ``ofPresentation, ``denominatorMap, ``ringMap, ``ringMap_algebraMap,
      ``ringMap_polynomialUnit, ``ringMap_fraction, ``map, ``ringMap_id,
      ``ringMap_comp, ``map_id, ``map_comp, ``map_ofPresentation, ``zeroValue,
      ``zeroValue_algebraMap, ``zeroValue_eq_one, ``toFractionRing,
      ``toFractionRing_algebraMap, ``toFractionRing_injective,
      ``toFractionRing_fraction, ``zeroSpecialization, ``oneSpecialization,
      ``actual_boundary_one, ``actual_ring_inclusion, ``identity_specialization] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual boundary-one rational functions use only standard Lean foundations."

end MotivicTest.BoundaryOneRationalFunctions
