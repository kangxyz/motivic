/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Polynomial.BoundaryOneRationalFunctions.Functor
public import Lean.Util.CollectAxioms

/-! # Direct consumers of the literal boundary-one rational homotopy -/

@[expose] public noncomputable section

open Polynomial.BoundaryOneRationalFunctions CategoryTheory
open scoped Polynomial

universe u v

namespace MotivicTest.BoundaryOneRationalHomotopy

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]

theorem actual_zero_endpoint (f : group R) :
    map (Polynomial.evalRingHom 0) (homotopy f) = 1 := homotopy_zero f

theorem actual_one_endpoint (f : group R) :
    map (Polynomial.evalRingHom 1) (homotopy f) = f := homotopy_one f

theorem actual_face_preservation (φ : R →+* S) (f : group R)
    (hf : map φ f = 1) : map (Polynomial.mapRingHom φ) (homotopy f) = 1 :=
  homotopy_preserves_face_one φ f hf

/-- There are no nontriviality or injectivity side conditions on the functor. -/
def actual_functor : CommRingCat.{u} ⥤ AddCommGrpCat.{u} := functor

open Lean in
run_cmd do
  for name in #[``fraction_val_mul, ``parameter, ``linear, ``exists_linear,
      ``homotopy, ``homotopy_val, ``ringMap_specialize_constant,
      ``ringMap_specialize_parameter, ``homotopy_zero, ``homotopy_one,
      ``homotopy_identity, ``ringMap_coefficient_naturality,
      ``ringMap_parameter, ``homotopy_natural, ``homotopy_preserves_face_one,
      ``functor, ``functor_map_apply, ``functor_map_eq_zero_iff,
      ``actual_zero_endpoint, ``actual_one_endpoint, ``actual_face_preservation,
      ``actual_functor] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual boundary-one rational homotopy uses only standard Lean foundations."

end MotivicTest.BoundaryOneRationalHomotopy
