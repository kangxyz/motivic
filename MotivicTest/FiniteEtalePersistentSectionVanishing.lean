/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtalePersistentSectionVanishing
import Lean

/-! # Arbitrary original small-Nis section detection and transitive trust audit -/

public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Topology
open Motivic.FiniteEtaleSite
universe u

/-- Direct consumer: the coefficient sheaf is genuinely arbitrary on the small site. -/
theorem arbitrary_small_sheaf_persistent_detection
    {U X : Scheme.{u}} [IsNoetherian U] (g : U ⟶ X) (x : X)
    (G : Sheaf (Motivic.FiniteEtaleSite.nisnevichTopology U) AddCommGrpCat.{u + 1})
    (s : G.obj.obj (op (baseObject U)))
    (hs : ∀ z : U, g z ⤳ x →
      (residuePoint U z).toPresheafFiber (baseObject U)
        (residuePointElement U z) G.obj s = 0) :
    ∃ W : X.Opens, x ∈ W ∧
      G.obj.map (toBaseObject (openObject (g ⁻¹ᵁ W))).op s = 0 :=
  exists_open_restriction_eq_zero_of_persistent_residue_germs g x G s hs

/-- The map used in the conclusion is the original open-subscheme inclusion. -/
example {U X : Scheme.{u}} [IsNoetherian U] (g : U ⟶ X) (W : X.Opens) :
    (toBaseObject (openObject (g ⁻¹ᵁ W))).left = (g ⁻¹ᵁ W).ι := rfl

open Lean in
run_cmd do
  for name in #[``arbitrary_small_sheaf_persistent_detection,
      ``exists_open_restriction_eq_zero_of_persistent_residue_germs,
      ``open_restriction_eq_zero_of_residue_splitting_family,
      ``exists_residue_splitting_zero_neighborhood] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Arbitrary small-Nis persistent section detection: standard foundations only."
