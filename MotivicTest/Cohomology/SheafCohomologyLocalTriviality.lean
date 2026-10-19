/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.LocalTriviality
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Lean.Util.CollectAxioms
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Motivic.Transfers.Sheaf.Basic

/-!
# Actual smooth Nisnevich covers killing ordinary cohomology classes

Ordinary enough injectives are obtained from the actual essentially-small
smooth site and the Grothendieck category of abelian groups. No acyclicity of
transfer injectives is assumed. The direct consumers retain standard Ext and
original transfer coefficient universes, and produce genuine covering sieves
or actual smooth Nisnevich covering families with the original restrictions.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite Motivic

universe u

namespace MotivicTest.Cohomology.SheafCohomologyLocalTriviality

variable (k : Type u) [Field k]

local instance : IsGrothendieckAbelian.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) := by
  let : SmallCategory.{u + 1}
      (SmallModel.{u + 1, u, u + 1} (SmoothSite (Spec (.of k)))) :=
    smallCategorySmallModel.{u + 1, u, u + 1} _
  let J' : GrothendieckTopology
      (SmallModel.{u + 1, u, u + 1} (SmoothSite (Spec (.of k)))) :=
    (equivSmallModel.{u + 1, u, u + 1} (SmoothSite (Spec (.of k)))).inverse.inducedTopology
      (SmoothSite.nisnevichTopology (Spec (.of k)))
  let : HasSheafify J' AddCommGrpCat.{u + 1} := inferInstance
  exact @Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1, u + 1, u, u + 2, u + 1}
    (SmoothSite (Spec (.of k))) inferInstance inferInstance
    (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}
    inferInstance inferInstance inferInstance (fun _ => inferInstance)
    (show HasSheafify J' AddCommGrpCat.{u + 1} from inferInstance)

local instance : HasExt.{u + 2}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  HasExt.standard _

/-- A literal ordinary H1 class is killed on an actual cokernel-section image sieve. -/
theorem actual_H_one_image_sieve
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (X : SmoothSite (Spec (.of k)))
    (x : _root_.CategoryTheory.Sheaf.LargeCohomology.H.{u + 2, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) F 1 X) :
    ∃ s : (cokernel (Injective.ι F)).obj.obj (op X),
      Presheaf.imageSieve (cokernel.π (Injective.ι F)).hom s ∈
        SmoothSite.nisnevichTopology (Spec (.of k)) X ∧
      ∀ ⦃Y : SmoothSite (Spec (.of k))⦄ (f : Y ⟶ X),
        Presheaf.imageSieve (cokernel.π (Injective.ι F)).hom s f →
          (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 2, u + 1, u, u + 1}
            (SmoothSite.nisnevichTopology (Spec (.of k))) F 1).map f.op x = 0 :=
  _root_.CategoryTheory.Sheaf.LargeCohomology.exists_imageSieve_restriction_eq_zero_one _ F X x

/-- Original ordinary classes of transfer sheaves vanish on an actual smooth Nisnevich family. -/
theorem actual_transfer_class_cover (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (X : SmoothSite (Spec (.of k)))
    (x : _root_.CategoryTheory.Sheaf.LargeCohomology.H.{u + 2, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf.{u + 1} k).obj F) (n + 1) X) :
    ∃ P : Presieve X, P ∈ SmoothSite.nisnevichPrecoverage (Spec (.of k)) X ∧
      ∀ ⦃Y : SmoothSite (Spec (.of k))⦄ (f : Y ⟶ X), P f →
        (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 2, u + 1, u, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf.{u + 1} k).obj F) (n + 1)).map f.op x = 0 := by
  obtain ⟨P, hP, hPQ⟩ := SmoothSite.mem_nisnevichTopology_iff.mp
    (_root_.CategoryTheory.Sheaf.LargeCohomology.zeroSieve_mem_succ _ _ n X x)
  refine ⟨P, hP, ?_⟩
  intro Y f hf
  have h := hPQ _ _ hf
  simpa only [Presheaf.equalizerSieve_apply, map_zero] using h

open Lean in
run_cmd do
  for name in #[``actual_H_one_image_sieve, ``actual_transfer_class_cover] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual ordinary cohomology local triviality uses only standard Lean foundations."

end MotivicTest.Cohomology.SheafCohomologyLocalTriviality
