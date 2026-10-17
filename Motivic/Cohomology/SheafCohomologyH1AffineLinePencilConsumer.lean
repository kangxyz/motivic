/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Cohomology.SheafCohomologyH1AffineLineGeometryConsumer
public import Motivic.AlgebraicGeometry.Correspondences.DiagonalSignedPencilProducer

/-! # Killing the actual affine-line H¹ class from genuine section-pencil data -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u
namespace Motivic.SheafCohomology
open AffineLineReducedComplement

variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [EnoughInjectives
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The original class vanishes from actual Cartesian section data, with no
endpoint correspondence equations assumed. The target is the original overlap,
not the generic open; the two source legs are the exact refined-square maps. -/
theorem h_one_eq_zero_of_affineLine_section_pencil
    (F : SheafWithTransfers.{u + 1} k)
    (hF : PresheafWithTransfers.IsA1Invariant F.obj)
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1 (SmoothSite.affineLine (.of k))) :
    let D := affineLineH1LiftData ((SheafWithTransfers.toSheaf k).obj F) x
    ∀ {Y' : SmoothSite (Spec (.of k))} (r : Y' ⟶ D.Y)
      [Etale (r ≫ D.p).left] [IsIso (pullback.snd (r ≫ D.p).left (inclusion D.U))],
      DiagonalSignedPencilProducer.Data (D.refinedSquare r).f₁₃
        (D.refinedSquare r).f₁₂ (D.overlapMap r) → x = 0 := by
  intro D Y' r hEt hIso P
  exact h_one_eq_zero_of_affineLine_correcting_homotopy F hF x r
    P.lam P.psi P.correspondence P.endpoints.1 P.endpoints.2

end Motivic.SheafCohomology
