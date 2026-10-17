/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.FirstObstructionLiftHI
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleA1BaseChangeNaturality

/-! # Original HI and lower-degree HI supply the actual first-obstruction lift -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.SheafWithTransfers
open FiniteEtaleSite
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (F : SheafWithTransfers.{u + 1} k)
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology (SmoothSite.a1Cylinder (.of k) X).left)
    AddCommGrpCat.{u + 1})]

/-- The obstruction is evaluated on the literal original neighborhood cylinder. -/
def a1TestObstruction (N : ℕ) (V : FiniteEtaleSite X.left)
    (α : SheafCohomology.H.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) N
        (SmoothSite.a1Cylinder (.of k) ((toSmoothSite X).obj V))) :
    (((directImage (SmoothSite.a1Projection (.of k) X).left).rightDerived N).obj
      ((restrict (SmoothSite.a1Cylinder (.of k) X) AddCommGrpCat.{u + 1}).obj
        ((toSheaf k).obj F))).obj.obj (Opposite.op V) :=
  originalFirstObstruction (SmoothSite.a1Projection (.of k) X) ((toSheaf k).obj F) N V
    ((SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toSheaf k).obj F) N).map (a1BaseChangeIso (.of k) X V).hom.op α)

/-- After shrinking, the lift is along the literal projection of the actual cylinder. -/
theorem a1_exists_open_projection_lift
    (hF : F.obj.IsA1Invariant) (N : ℕ) (hN : 0 < N)
    (hLow : ∀ q : ℕ, 0 < q → q < N →
      (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (V : FiniteEtaleSite X.left) [IsNoetherian V.left]
    {Z : Scheme.{u}} (g : V.left ⟶ Z) (z : Z)
    (α : SheafCohomology.H.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) N
        (SmoothSite.a1Cylinder (.of k) ((toSmoothSite X).obj V)))
    (hα : ∀ y : V.left, g y ⤳ z →
      markedSectionGerm
        (((directImage (SmoothSite.a1Projection (.of k) X).left).rightDerived N).obj
          ((restrict (SmoothSite.a1Cylinder (.of k) X) AddCommGrpCat.{u + 1}).obj
            ((toSheaf k).obj F))).obj V y (a1TestObstruction X F N V α) = 0) :
    ∃ O : Z.Opens, z ∈ O ∧ ∃ β,
      A1.projectionPullback (.of k)
        (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((toSheaf k).obj F) N) ((toSmoothSite X).obj (testOpenObject V (g ⁻¹ᵁ O))) β =
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((toSheaf k).obj F) N).map
          (SmoothSite.a1Map (.of k) ((toSmoothSite X).map
            (testOpenInclusion V (g ⁻¹ᵁ O)))).op α := by
  let P := SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
    ((toSheaf k).obj F) N
  obtain ⟨O, hz, β, hβ⟩ := a1_exists_open_originalRestriction_lift X F hF N hN hLow V g z
    (P.map (a1BaseChangeIso (.of k) X V).hom.op α) hα
  refine ⟨O, hz, β, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    (P.map (a1BaseChangeIso (.of k) X (testOpenObject V (g ⁻¹ᵁ O))).hom.op)).1
  change P.map _ (P.map _ β) = P.map _ (P.map _ α)
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    a1BaseChangeIso_hom_projection]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    ← a1BaseChangeIso_naturality, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply]
  exact hβ

end Motivic.SheafWithTransfers
