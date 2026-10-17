/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafCohomologyH1Descent
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Lean.Util.CollectAxioms

/-!
# Actual Nisnevich local lifts and the ordinary H1 coboundary criterion

These consumers retain arbitrary fields, original transfer coefficient
universes and standard ordinary Ext. Ordinary enough injectives are inferred
from the actual smooth site. Pairwise intersections are supplied by the
actual Nisnevich precoverage, with no assumption of arbitrary pullbacks.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite Motivic

universe u

namespace MotivicTest.Cohomology.SheafCohomologyH1Descent

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

variable (F : SheafWithTransfers.{u + 1} k)

local notation "J" => SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))
local notation "F₀" => Functor.obj (SheafWithTransfers.toSheaf k) F

/-- Every original coefficient H1 class has a quotient section with actual Nisnevich local lifts. -/
theorem actual_transfer_class_local_lifts
    (X : SmoothSite (Spec (.of k)))
    (x : SheafCohomology.H.{u + 2, u + 1, u, u + 1} J F₀ 1 X) :
    ∃ s : (cokernel (Injective.ι F₀)).obj.obj (op X),
      SheafCohomology.injectiveSectionBoundary.{u + 2, u + 1, u, u + 1} J F₀ X s = x ∧
      ∃ (ι : Type (u + 1)) (U : ι → SmoothSite (Spec (.of k))) (p : ∀ i, U i ⟶ X),
        Presieve.ofArrows U p ∈ SmoothSite.nisnevichPrecoverage (Spec (.of k)) X ∧
        ∃ l : ∀ i, (Injective.under F₀).obj.obj (op (U i)),
          ∀ i, (cokernel.π (Injective.ι F₀)).hom.app (op (U i)) (l i) =
            (cokernel (Injective.ι F₀)).obj.map (p i).op s :=
  SheafCohomology.exists_nisnevich_local_lifts_of_h_one F₀ X x

/-- On the actual pairwise fiber product, the difference has a unique original F-section. -/
theorem actual_pairwise_difference
    {X : SmoothSite (Spec (.of k))}
    {ι : Type*} {U : ι → SmoothSite (Spec (.of k))} (p : ∀ i, U i ⟶ X)
    (hp : Presieve.ofArrows U p ∈ SmoothSite.nisnevichPrecoverage (Spec (.of k)) X)
    (s : (cokernel (Injective.ι F₀)).obj.obj (op X))
    (l : ∀ i, (Injective.under F₀).obj.obj (op (U i)))
    (hl : ∀ i, (cokernel.π (Injective.ι F₀)).hom.app (op (U i)) (l i) =
      (cokernel (Injective.ι F₀)).obj.map (p i).op s) (i j : ι) :
    let _ := (SmoothSite.nisnevichPrecoverage (Spec (.of k))).hasPairwisePullbacks_of_mem hp
    ∃! d : (F₀).obj.obj (op (pullback (p i) (p j))),
      (Injective.ι F₀).hom.app (op (pullback (p i) (p j))) d =
        (Injective.under F₀).obj.map (pullback.fst (p i) (p j)).op (l i) -
          (Injective.under F₀).obj.map (pullback.snd (p i) (p j)).op (l j) := by
  let : (Presieve.ofArrows U p).HasPairwisePullbacks :=
    (SmoothSite.nisnevichPrecoverage (Spec (.of k))).hasPairwisePullbacks_of_mem hp
  exact Sheaf.existsUnique_localLiftDifference J
    (SheafCohomology.injectivePresentation_shortExact.{u + 1, u, u + 1} J F₀) (p i) (p j)
    (pullback.fst _ _) (pullback.snd _ _) pullback.condition s (l i) (l j) (hl i) (hl j)

/-- A literal Cech coboundary kills the represented standard ordinary H1 class. -/
theorem actual_coboundary_kills_class
    {X : SmoothSite (Spec (.of k))}
    (x : SheafCohomology.H.{u + 2, u + 1, u, u + 1} J F₀ 1 X)
    (s : (cokernel (Injective.ι F₀)).obj.obj (op X))
    (hs : SheafCohomology.injectiveSectionBoundary.{u + 2, u + 1, u, u + 1} J F₀ X s = x)
    {ι : Type*} {U : ι → SmoothSite (Spec (.of k))} (p : ∀ i, U i ⟶ X)
    (hp : Presieve.ofArrows U p ∈ SmoothSite.nisnevichPrecoverage (Spec (.of k)) X)
    (l : ∀ i, (Injective.under F₀).obj.obj (op (U i)))
    (hl : ∀ i, (cokernel.π (Injective.ι F₀)).hom.app (op (U i)) (l i) =
      (cokernel (Injective.ι F₀)).obj.map (p i).op s)
    (a : ∀ i, (F₀).obj.obj (op (U i)))
    (ha : let _ :=
        (SmoothSite.nisnevichPrecoverage (Spec (.of k))).hasPairwisePullbacks_of_mem hp
      ∀ i j,
        (Injective.under F₀).obj.map (pullback.fst (p i) (p j)).op (l i) -
          (Injective.under F₀).obj.map (pullback.snd (p i) (p j)).op (l j) =
        (Injective.ι F₀).hom.app (op (pullback (p i) (p j)))
          ((F₀).obj.map (pullback.fst (p i) (p j)).op (a i) -
            (F₀).obj.map (pullback.snd (p i) (p j)).op (a j))) :
    x = 0 :=
  SheafCohomology.h_one_eq_zero_of_nisnevich_coboundary F₀ x s hs p hp l hl a ha

/-- The standard consumer keeps the covariant extension-class sign literally. -/
theorem actual_boundary_formula (X : SmoothSite (Spec (.of k)))
    (s : (cokernel (Injective.ι F₀)).obj.obj (op X)) :
    SheafCohomology.injectiveSectionBoundary.{u + 2, u + 1, u, u + 1} J F₀ X s =
      ((SheafCohomology.zeroSections.{u + 2, u + 1, u, u + 1} J
        (cokernel (Injective.ι F₀)) X).symm s).comp
        (SheafCohomology.injectivePresentation_shortExact.{u + 1, u, u + 1} J F₀).extClass rfl :=
  rfl

open Lean in
run_cmd do
  for name in #[``actual_transfer_class_local_lifts, ``actual_pairwise_difference,
      ``actual_coboundary_kills_class, ``actual_boundary_formula] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual H1 Cech descent uses only standard Lean foundations."

end MotivicTest.Cohomology.SheafCohomologyH1Descent
