/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.EdgeWindow
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Lean.Util.CollectAxioms

/-! Direct tests of finite-window results for the original ordinary cohomology edge map. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace MotivicTest.FiniteEtaleOrdinaryEdgeWindow
open _root_.AlgebraicGeometry.Scheme (EtaleSeparatedFiniteType)
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {S T : Scheme.{u}} (b : T ⟶ S)
local instance : HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _
local instance : HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

/-- The actual edge in degree one is always injective: its required window is empty. -/
theorem actual_edge_one_injective (V : EtaleSeparatedFiniteType S)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) :
    Function.Injective (ordinaryEdgeMap b V F 1) :=
  ordinaryEdgeMap_injective_of_rightDerived_window b V F 1 (fun q hq hqN => by omega)

/-- The upper-endpoint-inclusive vanishing window implies bijectivity of the original arrow. -/
theorem actual_edge_bijective (V : EtaleSeparatedFiniteType S)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) (N : ℕ)
    (hR : ∀ q : ℕ, 0 < q → q ≤ N → IsZero (((directImage b).rightDerived q).obj F)) :
    Function.Bijective (ordinaryEdgeMap b V F N) :=
  ordinaryEdgeMap_bijective_of_rightDerived_window b V F N hR

/-- The strictly smaller positive window gives injectivity of the original arrow. -/
theorem actual_edge_injective (V : EtaleSeparatedFiniteType S)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) (N : ℕ)
    (hR : ∀ q : ℕ, 0 < q → q < N → IsZero (((directImage b).rightDerived q).obj F)) :
    Function.Injective (ordinaryEdgeMap b V F N) :=
  ordinaryEdgeMap_injective_of_rightDerived_window b V F N hR

open Lean in
run_cmd do
  for name in #[``actual_edge_one_injective, ``actual_edge_bijective, ``actual_edge_injective,
      ``CategoryTheory.Adjunction.extEdge_hom_formula,
      ``CategoryTheory.Adjunction.extEdge_bijective_of_rightDerived_window,
      ``CategoryTheory.Adjunction.extEdge_injective_of_rightDerived_window,
      ``CategoryTheory.Adjunction.imageResolutionHomAddEquiv_augmentation] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original ordinary finite-window edge: standard axioms only."

end MotivicTest.FiniteEtaleOrdinaryEdgeWindow
