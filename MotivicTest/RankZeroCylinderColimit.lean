/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.RankZero.Vanishing
public import MotivicTest.RelativeGenericBaseCylinderZero
import all Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.RankZeroPointRefinement
import all Motivic.Cohomology.A1.LocalVanishing.RankZero.Colimit
import all Motivic.Cohomology.A1.LocalVanishing.RankZero.Vanishing
public import Lean.Util.CollectAxioms

/-! Arbitrary field-valued markers and the unchanged cylinder neighborhood index. -/

@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite EtaleSeparatedFiniteType)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u

namespace MotivicTest.RankZeroCylinderColimit
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Motivic _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType _root_.Motivic.FiniteEtaleSite

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (K : Type u) [Field K] (b : Spec (.of K) ⟶ X.left) (p : Spec (.of K))
  (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- No residue-field splitting or finite-type hypothesis on the field marker is added. -/
theorem field_marker_rank (V : EtaleSeparatedFiniteType X.left)
    (a : (relativeFieldPoint b K (𝟙 _)).fiber.obj V) :
    ringKrullDim (V.left.presheaf.stalk
      ((relativeFieldPointFiberEquiv b K (𝟙 _) V a).left p)) =
      ringKrullDim (X.left.presheaf.stalk (b p)) :=
  fieldPoint_stalk_rank_eq X K b p V a

/-- Every original indexed representative, rather than only a canonical base
representative, is killed by an arrow of that very index. The producer is explicit. -/
theorem original_index_representative_zero
    (hd : ringKrullDim (X.left.presheaf.stalk (b p)) = 0)
    (hgen : ∀ (Y : SmoothSite (Spec (.of k))) [IsAffine Y.left] [IsIntegral Y.left]
      (s : P.obj (op (SmoothSite.a1Cylinder (.of k) Y))),
      ∃ O : Y.left.Opens, genericPoint Y.left ∈ O ∧
        P.map (SmoothSite.a1Map (.of k) (SmoothSite.openInclusion Y O)).op s = 0)
    (V : (relativeFieldPoint b K (𝟙 _)).fiber.Elements)
    (s : (pointedCylinderValues (.of k) (relativeFieldPoint b K (𝟙 _)) P
      (pointedBase (.of k) (relativeFieldPoint b K (𝟙 _)))).obj (op V)) :
    ∃ (W : (relativeFieldPoint b K (𝟙 _)).fiber.Elements) (f : W ⟶ V),
      (pointedCylinderValues (.of k) (relativeFieldPoint b K (𝟙 _)) P
        (pointedBase (.of k) (relativeFieldPoint b K (𝟙 _)))).map f.op s = 0 :=
  exists_rank_zero_cylinder_restriction_zero X K b p P hd hgen V s

variable (F : SheafWithTransfers.{u + 1} k)
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The positive rank-zero result has no generic-vanishing, coefficient-change,
continuity, rational-marker or infinite-ground-field premise. -/
theorem original_rank_zero_cylinder_colimit (hF : F.obj.IsA1Invariant) (n : ℕ)
    (hd : ringKrullDim (X.left.presheaf.stalk (b p)) = 0) :
    IsZero (colimit (pointedCylinderValues (.of k) (relativeFieldPoint b K (𝟙 _))
      (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) (n + 1))
      (pointedBase (.of k) (relativeFieldPoint b K (𝟙 _))))) :=
  pointedCylinderColimit_isZero_of_rank_zero F hF n X K b p hd

/-- Detection at an arbitrary original marked test object uses its actual
residue field and the higher direct image on the unchanged original base. -/
theorem original_rank_zero_marked_higher_image (hF : F.obj.IsA1Invariant) (n : ℕ)
    (V : EtaleSeparatedFiniteType X.left) (x : V.left)
    (hd : ringKrullDim (V.left.presheaf.stalk x) = 0)
    [HasExt.{u + 1}
      (Sheaf (nisnevichTopology (SmoothSite.a1Cylinder (.of k) X).left)
        AddCommGrpCat.{u + 1})] :
    IsZero ((markedResiduePoint V x).sheafFiber.obj
      (((directImage (SmoothSite.a1Projection (.of k) X).left).rightDerived (n + 1)).obj
        ((restrict (SmoothSite.a1Cylinder (.of k) X) AddCommGrpCat).obj
          ((SheafWithTransfers.toSheaf k).obj F)))) :=
  markedProjectionFiber_isZero_of_rank_zero F hF n X V x hd

open Lean in
run_cmd do
  for name in #[``field_marker_rank,
      ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.fieldPoint_stalk_rank_eq,
      ``fieldPoint_eq_genericPoint_of_rank_zero,
      ``exists_integral_affine_point_open_refinement,
      ``original_index_representative_zero,
      ``exists_rank_zero_cylinder_restriction_zero,
      ``pointedCylinderColimit_isZero_of_rank_zero_generic_open_zero,
      ``projectionPointFiber_isZero_of_rank_zero_generic_open_zero,
      ``pointedCylinderColimit_isZero_of_rank_zero,
      ``residueCylinderColimit_isZero_of_rank_zero,
      ``projectionPointFiber_isZero_of_rank_zero,
      ``markedProjectionFiber_isZero_of_rank_zero,
      ``original_rank_zero_cylinder_colimit,
      ``original_rank_zero_marked_higher_image] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual field markers and positive rank-zero cylinder germs: standard foundations only."

open Lean Batteries.Tactic.Lint in
run_cmd do
  let declarations := #[``field_marker_rank,
    ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.fieldPoint_stalk_rank_eq,
    ``fieldPoint_eq_genericPoint_of_rank_zero,
    ``exists_integral_affine_point_open_refinement,
    ``original_index_representative_zero,
    ``exists_rank_zero_cylinder_restriction_zero,
    ``pointedCylinderColimit_isZero_of_rank_zero_generic_open_zero,
    ``projectionPointFiber_isZero_of_rank_zero_generic_open_zero,
    ``pointedCylinderColimit_isZero_of_rank_zero,
    ``residueCylinderColimit_isZero_of_rank_zero,
    ``projectionPointFiber_isZero_of_rank_zero,
    ``markedProjectionFiber_isZero_of_rank_zero,
    ``original_rank_zero_cylinder_colimit,
    ``original_rank_zero_marked_higher_image]
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters were selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      throwError "{linter.name}: {name}: {message}"
  logInfo "Actual field markers and positive rank-zero cylinder germs: declaration linters passed."

end MotivicTest.RankZeroCylinderColimit
