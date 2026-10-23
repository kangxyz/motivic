/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ExtRightDerivedFunctoriality
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.DerivedSections
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Lean.Util.CollectAxioms

/-! Direct audit of original ordinary cohomology on actual geometric neighborhoods. -/
@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (EtaleSeparatedFiniteType)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace MotivicTest.ExtRightDerived
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {S T : Scheme.{u}} (b : T ⟶ S) (V : EtaleSeparatedFiniteType S)

local instance : HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

/-- The original Ext group is computed by actual right-derived neighborhood sections. -/
def originalOrdinarySections
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) (n : ℕ) :
    _root_.CategoryTheory.Sheaf.LargeCohomology.H.{u + 1, u + 1, u, u + 1}
      (nisnevichTopology T) F n ((baseChange b).obj V) ≃+
        (((pulledBackNeighborhoodSections b V).rightDerived n).obj F) :=
  ordinaryNeighborhoodDerivedSections b V (injectiveResolution F) n

open Lean in
run_cmd do
  for name in #[``originalOrdinarySections,
      ``CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv,
      ``CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_symm_hom,
      ``CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_naturality_left,
      ``CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_naturality_right] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original Ext, actual derived sections, and both genuine naturalities: standard axioms."

end MotivicTest.ExtRightDerived
