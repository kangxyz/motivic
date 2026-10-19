/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.Obstruction.CylinderLiftHI
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.BaseOpenPuncture
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian
public import Motivic.Cohomology.A1.LocalVanishing.Puncture.PointDiagrams

/-! # Genuine punctured projection lifts on the unchanged point index -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf
variable {k : Type u} [Field k] {X U : SmoothSite (Spec (.of k))} (j : U ⟶ X)
  (K : Type u) [Field K] (b : Spec (.of K) ⟶ X.left) (p : Spec (.of K))
  (F : SheafWithTransfers.{u + 1} k)
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology U.left) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology (SmoothSite.a1Cylinder (.of k) U).left)
    AddCommGrpCat.{u + 1})]

/-- The remaining inner induction input is literal marked higher-image fiber vanishing
at the persistent points of each actual punctured neighborhood. -/
def PersistentPunctureImageZero (N : ℕ) : Prop :=
  ∀ (V : EtaleSeparatedFiniteType X.left) (a : (relativeFieldPoint b K (𝟙 _)).fiber.obj V)
    (y : ((baseChange j.left).obj V).left),
    pullback.fst V.hom j.left y ⤳ (relativeFieldPointFiberEquiv b K (𝟙 _) V a).left p →
      IsZero ((markedResiduePoint ((baseChange j.left).obj V) y).sheafFiber.obj
        (((directImage (SmoothSite.a1Projection (.of k) U).left).rightDerived N).obj
          ((restrict (SmoothSite.a1Cylinder (.of k) U) AddCommGrpCat.{u + 1}).obj
            ((SheafWithTransfers.toSheaf k).obj F))))

/-- Every class acquires a literal projection lift on an actual refinement of its original
field-point neighborhood; the puncture/open exchange retains the original restriction map. -/
theorem exists_pointed_puncture_projection_lift
    (hF : F.obj.IsA1Invariant) (N : ℕ) (hN : 0 < N)
    (hLow : ∀ q : ℕ, 0 < q → q < N →
      (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (hG : PersistentPunctureImageZero j K b p F N)
    (V : EtaleSeparatedFiniteType X.left) (a : (relativeFieldPoint b K (𝟙 _)).fiber.obj V)
    (α : LargeCohomology.H.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((SheafWithTransfers.toSheaf k).obj F) N
        (SmoothSite.a1Cylinder (.of k) ((toSmoothSite U).obj ((baseChange j.left).obj V)))) :
    ∃ (V' : EtaleSeparatedFiniteType X.left) (a' : (relativeFieldPoint b K (𝟙 _)).fiber.obj V')
      (f : V' ⟶ V), (relativeFieldPoint b K (𝟙 _)).fiber.map f a' = a ∧ ∃ β,
      A1.projectionPullback (.of k)
        (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k))) ((SheafWithTransfers.toSheaf k).obj F) N)
        ((toSmoothSite U).obj ((baseChange j.left).obj V')) β =
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((SheafWithTransfers.toSheaf k).obj F) N).map
          (SmoothSite.a1Map (.of k) ((toSmoothSite U).map ((baseChange j.left).map f))).op α := by
  let P := LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) ((SheafWithTransfers.toSheaf k).obj F) N
  let W := (baseChange j.left).obj V
  let : IsNoetherian V.left := Scheme.isNoetherian_of_finiteType (show V.left ⟶ X.left from V.hom)
  let : IsNoetherian W.left := Scheme.isNoetherian_of_finiteType (show W.left ⟶ U.left from W.hom)
  let t := (relativeFieldPointFiberEquiv b K (𝟙 _) V a).left p
  have hα : ∀ y : W.left, pullback.fst V.hom j.left y ⤳ t →
      markedSectionGerm
        (((directImage (SmoothSite.a1Projection (.of k) U).left).rightDerived N).obj
          ((restrict (SmoothSite.a1Cylinder (.of k) U) AddCommGrpCat.{u + 1}).obj
            ((SheafWithTransfers.toSheaf k).obj F))).obj W y
          (F.a1TestObstruction U N W α) = 0 := by
    intro y hy
    exact ConcreteCategory.congr_hom
      ((IsZero.iff_id_eq_zero _).mp (hG V a y hy)) _
  obtain ⟨O, ht, β, hβ⟩ := F.a1_exists_open_projection_lift U hF N hN hLow W
    (pullback.fst V.hom j.left) t α hα
  obtain ⟨a', ha⟩ := exists_point_open_refinement_of_mem K b V a p O ht
  let e := (toSmoothSite U).mapIso (baseOpenPunctureIso j.left V O)
  refine ⟨testOpenObject V O, a', testOpenInclusion V O, ha, P.map e.hom.op β, ?_⟩
  have he : e.hom ≫ (toSmoothSite U).map
      (testOpenInclusion W (pullback.fst V.hom j.left ⁻¹ᵁ O)) =
        (toSmoothSite U).map ((baseChange j.left).map (testOpenInclusion V O)) := by
    dsimp only [e, Functor.mapIso_hom]
    rw [← Functor.map_comp]
    exact congrArg (toSmoothSite U).map (baseOpenPunctureIso_hom_inclusion j.left V O)
  have hn := ConcreteCategory.congr_hom
    (A1.projectionPullback_naturality (.of k) P e.hom) β
  simp only [ConcreteCategory.comp_apply] at hn
  change A1.projectionPullback (.of k) P _ (P.map e.hom.op β) = _
  rw [hn, hβ]
  change P.map _ (P.map _ α) = _
  have he' : SmoothSite.a1Map (.of k) e.hom ≫
      SmoothSite.a1Map (.of k) ((toSmoothSite U).map
        (testOpenInclusion W (pullback.fst V.hom j.left ⁻¹ᵁ O))) =
        SmoothSite.a1Map (.of k) ((toSmoothSite U).map
          ((baseChange j.left).map (testOpenInclusion V O))) := by
    change (SmoothSite.parameterProduct (SmoothSite.affineLine (.of k))).map e.hom ≫
      (SmoothSite.parameterProduct (SmoothSite.affineLine (.of k))).map _ = _
    rw [← Functor.map_comp, he]
    rfl
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, he']

end Motivic.FiniteEtaleSite
