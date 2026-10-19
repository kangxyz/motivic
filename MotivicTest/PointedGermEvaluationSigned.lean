/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Pointed.Evaluation.Signed
public import Lean.Util.CollectAxioms

/-! Direct regression for signed original-germ evaluation and section compatibility. -/
@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory
open Opposite
open AlgebraicGeometry
open Motivic
open _root_.Motivic.PresheafWithTransfers
universe u
namespace MotivicTest.PointedGermEvaluationSigned
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))
  {X Y : SmoothSite (Spec (.of k))}

/-- The actual signed action agrees with the original action on global sections. -/
theorem actual_signed_section_action (δ : Cor.mk X ⟶ Cor.mk Y) (x : X.left)
    (s : P.sections (Cor.mk Y)) :
    correspondenceGermHom k P hP x δ
        (fun y => SmoothSite.sectionToNisnevichPoint.{u, 0} ((toPresheaf k).obj P) Y y s) =
      SmoothSite.sectionToNisnevichPoint.{u, 0} ((toPresheaf k).obj P) X x (P.transfer δ s) :=
  correspondenceGermHom_section k P hP δ x s

open Lean in
run_cmd do
  for name in #[``actual_signed_section_action, ``correspondenceGermHom,
      ``correspondenceGermHom_cycle, ``correspondenceGermHom_apply,
      ``correspondenceGermHom_section, ``generatorGermEvaluation_section] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Signed original-germ evaluation and actual sections: standard foundations only."

end MotivicTest.PointedGermEvaluationSigned
