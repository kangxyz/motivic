module
import Motivic.Cohomology.Sheaf.H1.AffineLineVanishing
/-! # Actual affine-line H¹ vanishing with no supplied geometric correction -/
noncomputable section
open _root_.AlgebraicGeometry.Scheme.SmoothSite (affineLine nisnevichTopology)
open CategoryTheory
open AlgebraicGeometry
open Motivic
open _root_.CategoryTheory.Sheaf.LargeCohomology
open _root_.Motivic.SheafCohomology
universe w u
variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [EnoughInjectives
    (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

example (F : SheafWithTransfers.{u + 1} k)
    (hF : PresheafWithTransfers.IsA1Invariant F.obj)
    (x : H.{w, u + 1, u, u + 1} (nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1 (affineLine (.of k))) : x = 0 :=
  h_one_affineLine_eq_zero F hF x

open Lean in
run_cmd do
  for axiomName in ← collectAxioms ``h_one_affineLine_eq_zero do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Affine-line H1 vanishing depends on unsupported assumption {axiomName}"
  logInfo "Actual affine-line H1 vanishing uses only standard Lean foundations."
