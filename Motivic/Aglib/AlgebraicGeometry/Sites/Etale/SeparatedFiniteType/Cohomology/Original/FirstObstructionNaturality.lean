/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Original.FirstObstruction
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.Persistent.ObstructionLift

/-! # First obstruction for the original big-site neighborhood restriction -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf
variable {B : Scheme.{u}} {X Y : SmoothSite B} (h : Y ⟶ X)
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology Y.left) AddCommGrpCat.{u + 1})]
  (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})

omit [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})] in
/-- Original big-site restrictions commute with the actual higher-image obstruction. -/
theorem originalFirstObstruction_naturality (N : ℕ) {V W : EtaleSeparatedFiniteType X.left}
    (a : V ⟶ W)
    (α : LargeCohomology.H.{u + 1, u + 1, u, u + 1} (SmoothSite.nisnevichTopology B)
      F N ((toSmoothSite Y).obj ((baseChange h.left).obj W))) :
    originalFirstObstruction h F N V
      ((LargeCohomology.presheaf (SmoothSite.nisnevichTopology B) F N).map
        ((toSmoothSite Y).map ((baseChange h.left).map a)).op α) =
      (((directImage h.left).rightDerived N).obj
        ((restrict Y AddCommGrpCat.{u + 1}).obj F)).obj.map a.op
          (originalFirstObstruction h F N W α) := by
  rw [originalFirstObstruction, originalFirstObstruction,
    cohomologyRestrictionEquiv_restriction, ordinaryFirstObstruction_naturality]

/-- Persistent obstruction germs supply an original big-site restriction lift after shrinking. -/
theorem exists_open_originalRestriction_lift_of_persistent_obstruction_germs
    [IsIso (restrictionToDirectImage F h)]
    (N : ℕ) (hN : 0 < N) (V : EtaleSeparatedFiniteType X.left) [IsNoetherian V.left]
    {Z : Scheme.{u}} (g : V.left ⟶ Z) (z : Z)
    (hR : ∀ q : ℕ, 0 < q → q < N →
      IsZero (((directImage h.left).rightDerived q).obj
        ((restrict Y AddCommGrpCat.{u + 1}).obj F)))
    (α : LargeCohomology.H.{u + 1, u + 1, u, u + 1} (SmoothSite.nisnevichTopology B)
      F N ((toSmoothSite Y).obj ((baseChange h.left).obj V)))
    (hα : ∀ y : V.left, g y ⤳ z →
      markedSectionGerm (((directImage h.left).rightDerived N).obj
        ((restrict Y AddCommGrpCat.{u + 1}).obj F)).obj V y
          (originalFirstObstruction h F N V α) = 0) :
    ∃ O : Z.Opens, z ∈ O ∧ ∃ β,
      (LargeCohomology.presheaf (SmoothSite.nisnevichTopology B) F N).map
        ((restrictionProjection h).app (testOpenObject V (g ⁻¹ᵁ O))).op β =
      (LargeCohomology.presheaf (SmoothSite.nisnevichTopology B) F N).map
        ((toSmoothSite Y).map ((baseChange h.left).map
          (testOpenInclusion V (g ⁻¹ᵁ O)))).op α := by
  obtain ⟨O, hz, hO⟩ :=
    exists_open_test_restriction_eq_zero_of_persistent_marked_germs
      (((directImage h.left).rightDerived N).obj
        ((restrict Y AddCommGrpCat.{u + 1}).obj F)) V g z
          (originalFirstObstruction h F N V α) hα
  refine ⟨O, hz, ?_⟩
  apply (originalFirstObstruction_eq_zero_iff h F N hN _ hR _).mp
  rw [originalFirstObstruction_naturality]
  exact hO

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
