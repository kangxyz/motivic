/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtalePersistentObstructionLift
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Lean.Util.CollectAxioms

/-! Actual ordinary first-obstruction exactness and transitive trust audit. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace MotivicTest.FiniteEtalePersistentObstructionLift
open Motivic Motivic.FiniteEtaleSite
variable {S T : Scheme.{u}} (b : T ⟶ S)
local instance : HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _
local instance : HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

/-- The actual original restriction of a class gains an original edge preimage after shrinking. -/
theorem actual_persistent_lift (V : FiniteEtaleSite S) [IsNoetherian V.left]
    {X : Scheme.{u}} (g : V.left ⟶ X) (x : X)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) (N : ℕ) (hN : 0 < N)
    (hR : ∀ q : ℕ, 0 < q → q < N → IsZero (((directImage b).rightDerived q).obj F))
    (α : SheafCohomology.H.{u + 1, u + 1, u, u + 1}
      (nisnevichTopology T) F N ((baseChange b).obj V))
    (hα : ∀ z : V.left, g z ⤳ x →
      markedSectionGerm (((directImage b).rightDerived N).obj F).obj V z
        (ordinaryFirstObstruction b V F N α) = 0) :
    ∃ O : X.Opens, x ∈ O ∧ ∃ β,
      ordinaryEdgeMap b (testOpenObject V (g ⁻¹ᵁ O)) F N β =
        (SheafCohomology.presheaf (nisnevichTopology T) F N).map
          ((baseChange b).map (testOpenInclusion V (g ⁻¹ᵁ O))).op α :=
  exists_open_ordinaryEdge_lift_of_persistent_obstruction_germs b V g x F N hN hR α hα

open Lean in
run_cmd do
  for name in #[``actual_persistent_lift,
      ``Motivic.FiniteEtaleSite.ordinaryFirstObstruction_naturality,
      ``CategoryTheory.Adjunction.extFirstObstruction_naturality] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Persistent obstruction and actual edge lift: standard axioms only."

end MotivicTest.FiniteEtalePersistentObstructionLift
