/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.FirstObstructionNaturality
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.Persistent.MarkedSection

/-! # Persistent first-obstruction germs give genuine ordinary edge lifts -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf
variable {S T : Scheme.{u}} (b : T ⟶ S)
  [HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})]

/-- Only persistent degree-zero germs of the genuine obstruction section are needed;
no higher cohomology vanishing of the obstruction sheaf is assumed. -/
theorem exists_open_ordinaryEdge_lift_of_persistent_obstruction_germs
    (V : EtaleSeparatedFiniteType S) [IsNoetherian V.left] {X : Scheme.{u}}
    (g : V.left ⟶ X) (x : X)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) (N : ℕ) (hN : 0 < N)
    (hR : ∀ q : ℕ, 0 < q → q < N → IsZero (((directImage b).rightDerived q).obj F))
    (α : LargeCohomology.H.{u + 1, u + 1, u, u + 1}
      (nisnevichTopology T) F N ((baseChange b).obj V))
    (hα : ∀ z : V.left, g z ⤳ x →
      markedSectionGerm (((directImage b).rightDerived N).obj F).obj V z
        (ordinaryFirstObstruction b V F N α) = 0) :
    ∃ O : X.Opens, x ∈ O ∧ ∃ β,
      ordinaryEdgeMap b (testOpenObject V (g ⁻¹ᵁ O)) F N β =
        (LargeCohomology.presheaf (nisnevichTopology T) F N).map
          ((baseChange b).map (testOpenInclusion V (g ⁻¹ᵁ O))).op α := by
  obtain ⟨O, hx, hO⟩ :=
    exists_open_test_restriction_eq_zero_of_persistent_marked_germs
      (((directImage b).rightDerived N).obj F) V g x
      (ordinaryFirstObstruction b V F N α) hα
  refine ⟨O, hx, ?_⟩
  apply (ordinaryFirstObstruction_eq_zero_iff b _ F N hN hR _).mp
  rw [ordinaryFirstObstruction_naturality]
  exact hO

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
