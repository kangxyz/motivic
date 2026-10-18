/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafCohomologyContractionSheafZero
public import Motivic.Cohomology.A1.ContractionIntegralWholeZeroRefinement
import all Motivic.Aglib.CategoryTheory.Sites.SheafifyLocallyZero
import all Motivic.AlgebraicGeometry.PresheavesWithTransfers.NisnevichLocalZero
import all Motivic.Cohomology.A1.DenseOpenLocalDetection
import all Motivic.Cohomology.A1.PresheafGenericModelDetection
import all Motivic.Cohomology.A1.FiniteEtaleGenericModelDetection
import all Motivic.Cohomology.SheafCohomologyContractionSheafZero
import all Motivic.Cohomology.A1.ContractionIntegralWholeZeroRefinement
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint

/-! # Original generic detection and contraction-sheaf zero consumers -/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.SheafCohomologyContractionSheafZero

variable (k : Type u) [Field k] [Infinite k]

example (X : SmoothSite (Spec (.of k)))
    (W : FiniteEtaleSite (SmoothSite.a1Cylinder (.of k) X).left)
    (w : ((FiniteEtaleSite.baseChange (SmoothSite.a1Section (.of k) X 0).left).obj W).left) :
    ∃ (V : FiniteEtaleSite X.left)
      (v : V ⟶ (FiniteEtaleSite.baseChange (SmoothSite.a1Section (.of k) X 0).left).obj W),
      IsAffine V.left ∧ IsIntegral V.left ∧ IsOpenImmersion v.left ∧ w ∈ Set.range v.left := by
  obtain ⟨V, v, hV, hI, hv, hw, _⟩ :=
    FiniteEtaleSite.exists_integral_whole_zero_neighborhood_refinement X W w
  exact ⟨V, v, hV, hI, hv, hw⟩

example {X A : SmoothSite (Spec (.of k))} (a : A ⟶ X) [IsOpenImmersion a.left]
    (ha : DenseRange a.left) (P : PresheafWithTransfers.{u + 1} k)
    (hP : P.IsA1Invariant) (s : P.sections (Cor.mk X))
    (hs : P.transfer ((Cor.graphFunctor k).map a) s = 0) :
    (⨆ O : {O : X.left.Opens // P.smoothAffineZeroOpen X s O}, O.val) = ⊤ :=
  P.iSup_zero_opens_of_dense_open a ha hP s hs

example (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hG : ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
      (s : PresheafWithTransfers.genericModelGerm.{0, u} P X), s = 0) :
    IsZero ((PresheafWithTransfers.nisnevichSheafify k).obj P) :=
  P.isZero_nisnevichSheafify_of_genericModelGerm_eq_zero hP hG

variable [HasExt.{u + 1}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

example (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (SheafCohomology.withTransfers k F (n + 1)).IsA1Invariant) :
    IsZero ((PresheafWithTransfers.nisnevichSheafify k).obj
      (PresheafWithTransfers.contraction (SheafCohomology.withTransfers k F (n + 1)))) :=
  SheafCohomology.isZero_nisnevichSheafify_contraction_succ k F n hP

example (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (SheafCohomology.withTransfers k F (n + 1)).IsA1Invariant) :
    PresheafWithTransfers.toNisnevichSheafify k
      (PresheafWithTransfers.contraction (SheafCohomology.withTransfers k F (n + 1))) = 0 :=
  SheafCohomology.toNisnevichSheafify_contraction_succ_eq_zero k F n hP

example (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (SheafCohomology.withTransfers k F (n + 1)).IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) :
    IsZero ((presheafToSheaf (FiniteEtaleSite.nisnevichTopology X.left)
      AddCommGrpCat.{u + 1}).obj
      ((FiniteEtaleSite.toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
        (PresheafWithTransfers.contraction (SheafCohomology.withTransfers k F (n + 1))))) :=
  SheafCohomology.isZero_smallSheafify_contraction_succ k F n hP X

open Lean in
run_cmd do
  for name in #[``PresheafWithTransfers.exists_zero_neighborhood_of_dense_open,
      ``Presheaf.isZero_sheafify_of_locally_zero,
      ``PresheafWithTransfers.isZero_nisnevichSheafify_of_locally_zero,
      ``PresheafWithTransfers.iSup_zero_opens_of_dense_open,
      ``PresheafWithTransfers.exists_generic_open_zero_of_genericModelGerm_eq_zero,
      ``PresheafWithTransfers.isZero_nisnevichSheafify_of_genericModelGerm_eq_zero,
      ``SheafCohomology.isZero_nisnevichSheafify_contraction_succ,
      ``SheafCohomology.toNisnevichSheafify_contraction_succ_eq_zero,
      ``FiniteEtaleSite.zeroSieve_mem_of_genericModelGerm_eq_zero,
      ``FiniteEtaleSite.isZero_sheafify_of_genericModelGerm_eq_zero,
      ``SheafCohomology.isZero_smallSheafify_contraction_succ,
      ``FiniteEtaleSite.exists_integral_whole_zero_neighborhood_refinement] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original generic detection and contraction sheaf zero: standard foundations only."

open Lean Batteries.Tactic.Lint in
run_cmd do
  let declarations := #[``Presheaf.isZero_sheafify_of_locally_zero,
    ``PresheafWithTransfers.isZero_nisnevichSheafify_of_locally_zero,
    ``PresheafWithTransfers.iSup_zero_opens_of_dense_open,
    ``PresheafWithTransfers.exists_generic_open_zero_of_genericModelGerm_eq_zero,
    ``PresheafWithTransfers.exists_zero_neighborhood_of_genericModelGerm_eq_zero,
    ``PresheafWithTransfers.zeroSieve_mem_of_genericModelGerm_eq_zero,
    ``PresheafWithTransfers.isZero_nisnevichSheafify_of_genericModelGerm_eq_zero,
    ``FiniteEtaleSite.zeroSieve_mem_of_genericModelGerm_eq_zero,
    ``FiniteEtaleSite.isZero_sheafify_of_genericModelGerm_eq_zero,
    ``SheafCohomology.isZero_nisnevichSheafify_contraction_succ,
    ``SheafCohomology.toNisnevichSheafify_contraction_succ_eq_zero,
    ``SheafCohomology.isZero_smallSheafify_contraction_succ,
    ``FiniteEtaleSite.exists_integral_whole_zero_neighborhood_refinement]
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters were selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      throwError "{linter.name}: {name}: {message}"
  logInfo "Original generic detection and both contraction sheafifications: declaration lint passed."

end MotivicTest.SheafCohomologyContractionSheafZero
