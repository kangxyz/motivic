/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Twists.Field

/-! # Whole finite-field-boundary units on a fixed source -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.CoherentGraph

namespace Motivic.MotivicTest.FieldBoundaryTwists
universe u

example (k : Type u) [Field k] (ι : Type u) {Z W : Scheme.{u}}
    (g : Z ⟶ ProjectiveSpace k ι) [IsFinite (g ≫ toSpec k ι)] (h : W ⟶ Z) (n : ℕ) :
    IsIso ((unitHomGlobalSectionsEquiv W
      ((Modules.pullback (h ≫ g)).obj (twistingSheaf k ι (n : ℤ)))).symm
        (fieldBoundaryTwistSection_baseChange k ι g h n)) :=
  fieldBoundaryTwistSection_baseChange_isIso k ι g h n

open Lean in
run_cmd do
  for name in #[``finiteFieldLineBundle_trivial, ``fieldBoundaryTwistOneIso,
      ``fieldBoundaryTwistIso, ``fieldBoundaryTwistIso_baseChange,
      ``fieldBoundaryTwistSection_baseChange_coefficient,
      ``fieldBoundaryTwistSection_baseChange_isIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole-boundary original-twist units use only standard foundations."

end Motivic.MotivicTest.FieldBoundaryTwists
