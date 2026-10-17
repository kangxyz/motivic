/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.NisnevichPersistentFiniteSubfamily
public import Lean.Util.CollectAxioms

/-! Actual open-puncture specialization of persistent residue-splitting reflection. -/
@[expose] public section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u v
namespace MotivicTest.NisnevichPersistentFiniteSubfamily

/-- The puncture is an actual open subscheme, with actual residue-field lifting. -/
theorem actual_open_puncture_finite_cover
    (X : Scheme.{u}) [IsNoetherian X] (U : X.Opens) (x : X)
    {ι : Type v} {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ U.toScheme)
    [∀ i, Etale (f i)]
    (hf : ∀ z : U.toScheme, U.ι z ⤳ x → ∃ (i : ι) (y : Y i),
      f i y = z ∧ IsIso ((f i).residueFieldMap y)) :
    ∃ (W : X.Opens), x ∈ W ∧ ∃ s : Finset ι,
      ∀ z : U.toScheme, U.ι z ∈ W → ∃ i ∈ s, ∃ y : Y i,
        f i y = z ∧ IsIso ((f i).residueFieldMap y) := by
  let : IsNoetherian U.toScheme := Motivic.isNoetherian_of_finiteType U.ι
  exact Motivic.Nisnevich.exists_open_finset_persistent_residueFieldLifting U.ι x f hf

open Lean in
run_cmd do
  for name in #[``actual_open_puncture_finite_cover,
      ``Motivic.Nisnevich.exists_open_finset_persistent_residueFieldLifting] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual persistent residue-splitting finite family: standard axioms only."

end MotivicTest.NisnevichPersistentFiniteSubfamily
