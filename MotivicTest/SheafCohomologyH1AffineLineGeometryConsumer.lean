/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Motivic.Cohomology.Sheaf.H1.AffineLineGeometryConsumer

/-! # The actual affine-line H¹ discrepancy consumed by geometric homotopies -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open _root_.AlgebraicGeometry.Scheme.SmoothSite (affineLine nisnevichTopology
  a1Cylinder a1Section)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace MotivicTest.AffineLineGeometryConsumer

open Motivic _root_.CategoryTheory.Sheaf.LargeCohomology _root_.Motivic.SheafCohomology

open _root_.AlgebraicGeometry.Scheme.AffineLineReducedComplement

variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [EnoughInjectives
    (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

example
    (F : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (x : H.{w, u + 1, u, u + 1} (nisnevichTopology (Spec (.of k)))
      F 1 (affineLine (.of k))) :
    IsAffineOpen (affineLineH1LiftData F x).U :=
  (affineLineH1LiftData F x).affine_open

example
    (F : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (x : H.{w, u + 1, u, u + 1} (nisnevichTopology (Spec (.of k)))
      F 1 (affineLine (.of k))) :
    IsAffine (openObject (affineLineH1LiftData F x).U).left := inferInstance

example
    (F : SheafWithTransfers.{u + 1} k)
    (hF : PresheafWithTransfers.IsA1Invariant F.obj)
    (x : H.{w, u + 1, u, u + 1} (nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1 (affineLine (.of k))) :
    let D := affineLineH1LiftData ((SheafWithTransfers.toSheaf k).obj F) x
    ∀ {Y' : SmoothSite (Spec (.of k))} (r : Y' ⟶ D.Y)
      [Etale (r ≫ D.p).left] [IsIso (pullback.snd (r ≫ D.p).left (inclusion D.U))]
      (lam : Cor.mk Y' ⟶ Cor.mk D.overlap)
      (ψ : Cor.mk (openObject D.U) ⟶ Cor.mk D.overlap)
      (α : Cor.mk (a1Cylinder (.of k) (D.refinedSquare r).X₁) ⟶ Cor.mk D.overlap),
      (Cor.graphFunctor k).map (a1Section (.of k) (D.refinedSquare r).X₁ 0) ≫ α =
        (Cor.graphFunctor k).map (D.overlapMap r) →
      (Cor.graphFunctor k).map (a1Section (.of k) (D.refinedSquare r).X₁ 1) ≫ α =
        (Cor.graphFunctor k).map (D.refinedSquare r).f₁₃ ≫ lam -
          (Cor.graphFunctor k).map (D.refinedSquare r).f₁₂ ≫ ψ →
      x = 0 :=
  h_one_eq_zero_of_affineLine_correcting_homotopy F hF x

open Lean in
run_cmd do
  for name in #[``affineLineH1LiftData,
      ``AffineLineH1LiftData.discrepancy_eq,
      ``AffineLineH1LiftData.restricted_discrepancy_eq,
      ``h_one_eq_zero_of_affineLine_correcting_homotopy] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Constructed affine-line H¹ geometry consumer uses only standard Lean foundations."

end MotivicTest.AffineLineGeometryConsumer
