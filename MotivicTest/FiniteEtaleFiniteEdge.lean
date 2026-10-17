/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOrdinaryEdgeMap
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ImageResolutionWindow
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Lean.Util.CollectAxioms

/-! Direct consumers of the actual image cone and actual ordinary edge arrow. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace MotivicTest.FiniteEtaleFiniteEdge
open Motivic Motivic.FiniteEtaleSite
variable {S T : Scheme.{u}} (b : T ⟶ S)
local instance : HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _
local instance : HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _
attribute [local instance] HasDerivedCategory.standard

/-- The actual degree-zero ordinary edge requires no acyclicity or comparison hypothesis. -/
theorem actual_ordinary_edge_zero (V : FiniteEtaleSite S)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) :
    Function.Bijective (ordinaryEdgeMap b V F 0) := ordinaryEdgeMap_zero_bijective b V F

/-- The actual direct-image cone has the stated finite bound from genuine R^q vanishing. -/
theorem actual_directImage_cone_window
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) (N : ℕ)
    (hR : ∀ q : ℕ, 0 < q → q ≤ N → IsZero (((directImage b).rightDerived q).obj F))
    (i : ℤ) (hi : i ≤ N) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((injectiveResolution F).imageTriangle (directImage b)).obj₃) :=
  (injectiveResolution F).imageTriangle_cone_homology_zero (directImage b) N hR i hi

open Lean in
run_cmd do
  for name in #[``actual_ordinary_edge_zero, ``actual_directImage_cone_window,
      ``CategoryTheory.Adjunction.extEdge_unit,
      ``CategoryTheory.InjectiveResolution.imageTriangle_postcomp_injective,
      ``CategoryTheory.InjectiveResolution.imageTriangle_postcomp_bijective] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual edge arrow and constructed finite-window cone: standard axioms."

end MotivicTest.FiniteEtaleFiniteEdge
