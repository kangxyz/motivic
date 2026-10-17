/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.NisnevichFiberSections
public import Lean.Util.CollectAxioms

/-!
# Whole-fiber Nisnevich lifting consumers

The finite-support application retains the actual fiber inclusion. No
reducedness, connectedness, nonemptiness, or flatness hypothesis is added.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace MotivicTest.NisnevichFiberSections

example {U Z S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p] (q : U ⟶ Z) [Etale q]
    (h : ∀ z : Z, ∃ x : U, q x = z ∧ IsIso (q.residueFieldMap x)) (s : S) :
    ∃ b : p.fiber s ⟶ U, b ≫ q = p.fiberι s :=
  p.exists_lift_from_quasiFiniteFiber_of_residueFieldIso q h s

example {R : Type u} [CommRing R] [IsArtinianRing R] {U Z : Scheme.{u}}
    (q : U ⟶ Z) [Etale q]
    (h : ∀ z : Z, ∃ x : U, q x = z ∧ IsIso (q.residueFieldMap x))
    (a : Spec (.of R) ⟶ Z) : ∃ b : Spec (.of R) ⟶ U, b ≫ q = a :=
  q.exists_lift_from_locallyArtinian_of_residueFieldIso h a

open Lean in
run_cmd do
  for name in #[``AlgebraicGeometry.Scheme.Hom.exists_lift_from_locallyArtinian_of_residueFieldIso,
      ``AlgebraicGeometry.Scheme.Hom.exists_lift_from_quasiFiniteFiber_of_residueFieldIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.NisnevichFiberSections
