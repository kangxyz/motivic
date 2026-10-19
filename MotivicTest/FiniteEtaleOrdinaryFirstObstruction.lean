/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.FirstObstruction
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Lean.Util.CollectAxioms

/-! Actual ordinary first-obstruction exactness and transitive trust audit. -/
@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (EtaleSeparatedFiniteType)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace MotivicTest.FiniteEtaleOrdinaryFirstObstruction
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {S T : Scheme.{u}} (b : T ⟶ S)
local instance : HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _
local instance : HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

/-- Neither a derived comparison nor an obstruction map is assumed. -/
theorem actual_first_obstruction_exact (V : EtaleSeparatedFiniteType S)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) (N : ℕ) (hN : 0 < N)
    (hR : ∀ q : ℕ, 0 < q → q < N → IsZero (((directImage b).rightDerived q).obj F))
    (x : _root_.CategoryTheory.Sheaf.LargeCohomology.H.{u + 1, u + 1, u, u + 1}
      (nisnevichTopology T) F N ((baseChange b).obj V)) :
    ordinaryFirstObstruction b V F N x = 0 ↔
      ∃ z, ordinaryEdgeMap b V F N z = x :=
  ordinaryFirstObstruction_eq_zero_iff b V F N hN hR x

open Lean in
run_cmd do
  for name in #[``actual_first_obstruction_exact,
      ``DerivedCategory.single_hom_eq_zero_of_first_homology,
      ``CategoryTheory.InjectiveResolution.imageFirstObstruction_naturality,
      ``CategoryTheory.Adjunction.imageResolutionExtAddEquiv_augmentation] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual first obstruction and original ordinary edge: standard axioms only."

end MotivicTest.FiniteEtaleOrdinaryFirstObstruction
