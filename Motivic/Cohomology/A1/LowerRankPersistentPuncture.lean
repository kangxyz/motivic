/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PersistentPuncturePointVanishing
public import Motivic.Cohomology.A1.PointedMarkedCylinderComparison
public import Motivic.Aglib.AlgebraicGeometry.StalkRankGenerization

/-! # Lower local rank induction supplies the persistent puncture fibers -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {k : Type u} [Field k] {X U : SmoothSite (Spec (.of k))} (j : U ⟶ X)
  (K : Type u) [Field K] (b : Spec (.of K) ⟶ X.left) (p : Spec (.of K))
  (F : SheafWithTransfers.{u + 1} k)
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology U.left) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology (SmoothSite.a1Cylinder (.of k) U).left)
    AddCommGrpCat.{u + 1})]

/-- The inner induction concerns original cylinder germs on actual smooth objects,
not a coefficient extended to a residue-field smooth site. -/
def LowerRankCylinderGermsZero (N d : ℕ) : Prop :=
  ∀ (Y : SmoothSite (Spec (.of k))) (y : Y.left),
    ringKrullDim (Y.left.presheaf.stalk y) < d →
      IsZero (colimit (pointedCylinderValues (.of k) (X := Y) (residuePoint Y.left y)
        (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k))) ((SheafWithTransfers.toSheaf k).obj F) N)
        (pointedBase (.of k) (X := Y) (residuePoint Y.left y))))

omit [HasExt.{u + 1} (Sheaf (nisnevichTopology U.left) AddCommGrpCat.{u + 1})] in
/-- A puncture excluding the center makes every persistent point a proper generization.
Actual etale stalk dimensions and the marked cylinder comparison then apply the inner IH. -/
theorem persistentPunctureImageZero_of_lowerRank [IsOpenImmersion j.left]
    (N d : ℕ) (hd : ringKrullDim (X.left.presheaf.stalk (b p)) = d)
    (hmiss : b p ∉ Set.range j.left) (hIH : LowerRankCylinderGermsZero F N d) :
    PersistentPunctureImageZero j K b p F N := by
  intro V a y hy
  let W := (baseChange j.left).obj V
  let t : V.left := (relativeFieldPointFiberEquiv b K (𝟙 _) V a).left p
  have ht : (show V.left ⟶ X.left from V.hom) t = b p := by
    have hw := Over.w (relativeFieldPointFiberEquiv b K (𝟙 _) V a)
    have he := congrArg (fun f : Spec (.of K) ⟶ X.left => f p) hw
    change (show V.left ⟶ X.left from V.hom) t = (𝟙 _ ≫ b) p at he
    simpa only [Category.id_comp] using he
  have hne : pullback.fst V.hom j.left y ≠ t := by
    intro he
    apply hmiss
    refine ⟨pullback.snd V.hom j.left y, ?_⟩
    have hc := congrArg (fun f : pullback V.hom j.left ⟶ X.left => f y)
      (pullback.condition (f := V.hom) (g := j.left))
    replace hc := hc.symm
    change j.left (pullback.snd V.hom j.left y) =
      (show V.left ⟶ X.left from V.hom) (pullback.fst V.hom j.left y) at hc
    exact hc.trans ((congrArg (fun z => (show V.left ⟶ X.left from V.hom) z) he).trans ht)
  let : IsNoetherian V.left := Motivic.isNoetherian_of_finiteType
    (show V.left ⟶ X.left from V.hom)
  have hdt : ringKrullDim (V.left.presheaf.stalk t) = d := by
    rw [Scheme.ringKrullDim_stalk_eq_of_etale (show V.left ⟶ X.left from V.hom) t, ht]
    exact hd
  have hr := Scheme.stalk_rank_lt_of_proper_generization hy hne d hdt
  have hry : ringKrullDim (W.left.presheaf.stalk y) < d := by
    rw [Scheme.ringKrullDim_stalk_eq_of_etale
      (show W.left ⟶ V.left from pullback.fst V.hom j.left) y]
    exact hr
  exact markedProjectionFiber_isZero_of_cylinderColimit (.of k) U W y
    ((SheafWithTransfers.toSheaf k).obj F) N (hIH ((toSmoothSite U).obj W) y hry)

variable [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology (SmoothSite.a1Cylinder (.of k) X).left)
    AddCommGrpCat.{u + 1})]

/-- The inner local-rank induction now supplies every persistent puncture fiber;
only the independent original restriction mono and puncture geometry remain. -/
theorem projectionPointFiber_isZero_of_lowerRank [IsOpenImmersion j.left]
    (hF : F.obj.IsA1Invariant) (n d : ℕ)
    (hd : ringKrullDim (X.left.presheaf.stalk (b p)) = d)
    (hmiss : b p ∉ Set.range j.left)
    (hLow : ∀ q : ℕ, 0 < q → q < n + 1 →
      (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (hIH : LowerRankCylinderGermsZero F (n + 1) d)
    [Mono (colim.map (pointedCylinderRestriction (.of k) j (relativeFieldPoint b K (𝟙 _))
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((SheafWithTransfers.toSheaf k).obj F)
          (n + 1))))] :
    IsZero ((relativeFieldPoint b K (𝟙 _)).sheafFiber.obj
      (((directImage (SmoothSite.a1Projection (.of k) X).left).rightDerived (n + 1)).obj
        ((restrict (SmoothSite.a1Cylinder (.of k) X) AddCommGrpCat.{u + 1}).obj
          ((SheafWithTransfers.toSheaf k).obj F)))) :=
  projectionPointFiber_isZero_of_persistent_puncture j K b p F hF n hLow
    (persistentPunctureImageZero_of_lowerRank j K b p F (n + 1) d hd hmiss hIH)

end Motivic.FiniteEtaleSite
