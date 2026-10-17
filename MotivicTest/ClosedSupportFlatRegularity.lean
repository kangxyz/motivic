/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ClosedSupportFlatRegularity

/-!
# Consumers of literal closed-support fiber regularity

Only the closed support's map is assumed flat. The ambient source is arbitrary,
and both its literal ideal-sheaf quotient and original stalk scalar are retained.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Polynomial

universe u

namespace MotivicTest.ClosedSupportFlatRegularity

/-- The actual closed-support quotient needs no whole-source flatness or reduction. -/
theorem arbitraryAmbientClosedSupport
    {k : Type u} [CommRing k] {C P : Scheme.{u}}
    (f : P ⟶ Spec (.of k[X])) (j : C ⟶ P) [IsClosedImmersion j]
    [Flat (j ≫ f)] (a : k) (c : C) :
    IsSMulRegular ((P.presheaf.stalk (j c)) ⧸ j.ker.stalk (j c))
      (f.stalkMap (j c) (StructureSheaf.toStalk k[X] (f (j c))
        (Polynomial.X - Polynomial.C a))) :=
  closedImmersion_polynomial_fiber_isSMulRegular f j a c

open Lean in
run_cmd do
  for name in #[``AlgebraicGeometry.flat_polynomial_fiber_stalk_isSMulRegular,
      ``AlgebraicGeometry.closedImmersion_polynomial_fiber_isSMulRegular,
      ``arbitraryAmbientClosedSupport] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Closed-support flat regularity uses only standard foundations."

end MotivicTest.ClosedSupportFlatRegularity
