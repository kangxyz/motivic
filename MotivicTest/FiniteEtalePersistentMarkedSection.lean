/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtalePersistentMarkedSection
import Lean

/-! # Persistent detection on arbitrary test objects of the unchanged small site -/

public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Topology
open Motivic.FiniteEtaleSite
universe u

/-- The original coefficient is a sheaf on S, while the section is evaluated on arbitrary V. -/
theorem original_test_section_persistent_detection
    {S X : Scheme.{u}}
    (G : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
    (V : Motivic.FiniteEtaleSite S) [IsNoetherian V.left]
    (g : V.left ⟶ X) (x : X) (s : G.obj.obj (op V))
    (hs : ∀ z : V.left, g z ⤳ x →
      (markedResiduePoint V z).toPresheafFiber V (markedResidueElement V z) G.obj s = 0) :
    ∃ O : X.Opens, x ∈ O ∧
      G.obj.map (testOpenInclusion V (g ⁻¹ᵁ O)).op s = 0 :=
  exists_open_test_restriction_eq_zero_of_persistent_marked_germs G V g x s hs

/-- The endpoint arrow is exactly the original open inclusion, not a coefficient comparison. -/
example {S : Scheme.{u}} (V : Motivic.FiniteEtaleSite S) [IsNoetherian V.left]
    (O : V.left.Opens) : (testOpenInclusion V O).left = O.ι := rfl

open Lean in
run_cmd do
  for name in #[``original_test_section_persistent_detection,
      ``exists_open_test_restriction_eq_zero_of_persistent_marked_germs] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original arbitrary-test-object persistent detection: standard foundations only."
