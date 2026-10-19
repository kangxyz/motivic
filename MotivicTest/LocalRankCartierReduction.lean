/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Stalk.Dimension.SmoothStalkFiniteRank
public import Motivic.Cohomology.A1.Cartier.PositiveRankReduction
import all Motivic.Aglib.AlgebraicGeometry.Stalk.Dimension.SmoothStalkFiniteRank
import all Motivic.Cohomology.A1.LocalVanishing.Cylinder.OpenComparison
import all Motivic.Cohomology.A1.Cartier.PositiveRankReduction
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint

/-! # Original-marked local-rank and Cartier reduction consumers -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace MotivicTest.LocalRankCartierReduction
open Motivic _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType _root_.Motivic.FiniteEtaleSite

/-- No perfectness or global dimension bound is needed for finite local rank. -/
theorem actual_stalk_finite_rank {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    ∃ d : ℕ, ringKrullDim (X.presheaf.stalk x) = d :=
  Scheme.exists_nat_ringKrullDim_stalk_of_smooth f x

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (K : Type u) [Field K] (b : Spec (.of K) ⟶ X.left) (p : Spec (.of K))

/-- An actual zero germ on an open implies zero at the unchanged original mark. -/
theorem original_germ_zero_of_open_zero (O : X.left.Opens) (hO : b p ∈ O)
    (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (h : IsZero (colimit (pointedCylinderValues (.of k)
      (X := (toSmoothSite X).obj (openObject O))
      (relativeFieldPoint (openFieldPointLift K b p O hO) K (𝟙 _)) P
      (pointedBase (.of k) (X := (toSmoothSite X).obj (openObject O))
        (relativeFieldPoint (openFieldPointLift K b p O hO) K (𝟙 _)))))) :
    IsZero (colimit (pointedCylinderValues (.of k) (relativeFieldPoint b K (𝟙 _)) P
      (pointedBase (.of k) (relativeFieldPoint b K (𝟙 _))))) :=
  h.of_iso (openFieldPointCylinderColimitIso X K b p O hO P).symm

variable [PerfectField k] (F : SheafWithTransfers.{u + 1} k)
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- If the original germ remains nonzero, the chosen actual Cartier complement
cannot have the required original restriction mono. This is not a strict-A1 theorem. -/
theorem nonzero_original_germ_obstructs_cartier_restriction_mono
    (hF : F.obj.IsA1Invariant) (n d : ℕ)
    (hd : ringKrullDim (X.left.presheaf.stalk (b p)) = d) (hpos : 0 < d)
    (hLow : ∀ q : ℕ, 0 < q → q < n + 1 →
      (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (hIH : LowerRankCylinderGermsZero F (n + 1) d)
    (hne : ¬ IsZero (colimit (pointedCylinderValues (.of k)
      (relativeFieldPoint b K (𝟙 _))
      (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((SheafWithTransfers.toSheaf k).obj F)
          (n + 1)) (pointedBase (.of k) (relativeFieldPoint b K (𝟙 _)))))) :
    let P := _root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((SheafWithTransfers.toSheaf k).obj F)
        (n + 1)
    ∃ (O : X.left.Opens) (hO : b p ∈ O), IsAffineOpen O ∧
      ∃ (Z : Scheme.{u}) (i : Z ⟶ O.toScheme),
        IsClosedImmersion i ∧ IsLocallyRankOne O.toScheme (Scheme.Hom.idealModule i) ∧
        Smooth (i ≫ O.ι ≫ X.hom) ∧ b p ∈ Set.range (i ≫ O.ι) ∧
        ∃ W : O.toScheme.Opens, Set.range i = (W : Set O.toScheme)ᶜ ∧
          ¬ Mono (colim.map (pointedCylinderRestriction (.of k)
            (SmoothSite.openInclusion ((toSmoothSite X).obj (openObject O)) W)
            (relativeFieldPoint (openFieldPointLift K b p O hO) K (𝟙 _)) P)) := by
  obtain ⟨O, hO, hAffine, Z, i, hi, hI, hs, hz, W, hW, hred⟩ :=
    exists_positive_rank_cartier_restriction_reduction X K b p F hF n d hd hpos hLow hIH
  exact ⟨O, hO, hAffine, Z, i, hi, hI, hs, hz, W, hW, fun hmono => hne (hred hmono)⟩

open Lean in
run_cmd do
  for name in #[``actual_stalk_finite_rank, ``original_germ_zero_of_open_zero,
      ``nonzero_original_germ_obstructs_cartier_restriction_mono,
      ``Scheme.exists_nat_ringKrullDim_stalk_of_smooth,
      ``fieldPointCylinderColimitIso, ``toPresheafFiber_fieldPointCylinderColimitIso_hom,
      ``openFieldPointLift_ι, ``openFieldPointLift_apply, ``openFieldPointCylinderColimitIso,
      ``exists_positive_rank_cartier_restriction_reduction] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original-marked local-rank and conditional Cartier reduction: standard axioms only."

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[`Motivic.Aglib.AlgebraicGeometry.Stalk.Dimension.SmoothStalkFiniteRank,
    `Motivic.Cohomology.A1.LocalVanishing.Cylinder.OpenComparison,
    `Motivic.Cohomology.A1.Cartier.PositiveRankReduction]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 11 do
    throwError "The local-rank and Cartier reduction declarations are missing from this lint."
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters were selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      throwError "{linter.name}: {name}: {message}"
  logInfo "Local-rank and Cartier reduction: all selected declaration linters passed."

end MotivicTest.LocalRankCartierReduction
