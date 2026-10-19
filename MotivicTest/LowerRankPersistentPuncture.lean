/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.Puncture.LowerRankPersistent
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Injectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Lean.Util.CollectAxioms

/-! # Genuine punctured projection lifts on the unchanged point index -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace MotivicTest.LowerRankPersistentPuncture
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Motivic _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType _root_.Motivic.FiniteEtaleSite
variable {k : Type u} [Field k] {X U : SmoothSite (Spec (.of k))} (j : U ⟶ X)
  (K : Type u) [Field K] (b : Spec (.of K) ⟶ X.left) (p : Spec (.of K))
  (F : SheafWithTransfers.{u + 1} k)
local instance : HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _
local instance (Y : SmoothSite (Spec (.of k))) : HasExt.{u + 1}
    (Sheaf (nisnevichTopology Y.left) AddCommGrpCat.{u + 1}) := hasExt_of_enoughInjectives _

/-- Persistent puncture fibers and the independent original restriction mono force the
actual projection point fiber to vanish. The punctured comparison is now proved internally. -/
theorem actual_pointFiber_isZero
    [IsOpenImmersion j.left] (hF : F.obj.IsA1Invariant) (n d : ℕ)
    (hd : ringKrullDim (X.left.presheaf.stalk (b p)) = d)
    (hmiss : b p ∉ Set.range j.left)
    (hLow : ∀ q : ℕ, 0 < q → q < n + 1 →
      (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (hIH : LowerRankCylinderGermsZero F (n + 1) d)
    [Mono (colim.map (pointedCylinderRestriction (.of k) j (relativeFieldPoint b K (𝟙 _))
      (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((SheafWithTransfers.toSheaf k).obj F)
          (n + 1))))] :
    IsZero ((relativeFieldPoint b K (𝟙 _)).sheafFiber.obj
      (((directImage (SmoothSite.a1Projection (.of k) X).left).rightDerived (n + 1)).obj
        ((restrict (SmoothSite.a1Cylinder (.of k) X) AddCommGrpCat.{u + 1}).obj
          ((SheafWithTransfers.toSheaf k).obj F)))) :=
  projectionPointFiber_isZero_of_lowerRank j K b p F hF n d hd hmiss hLow hIH

open Lean in
run_cmd do
  for name in #[``actual_pointFiber_isZero,
      ``Motivic.FiniteEtaleSite.markedCylinderColimitFiberIso,
      ``AlgebraicGeometry.Scheme.stalk_rank_lt_of_proper_generization,
      ``Motivic.FiniteEtaleSite.persistentPunctureImageZero_of_lowerRank,
      ``Motivic.FiniteEtaleSite.pointedPunctureProjection_colimit_isIso,
      ``baseOpenPunctureIso_hom_inclusion,
      ``exists_point_open_refinement_of_mem] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual lower local rank induction and point vanishing: standard axioms only."

end MotivicTest.LowerRankPersistentPuncture
