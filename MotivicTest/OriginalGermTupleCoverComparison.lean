/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Tuples.CoverComparison
public import Lean.Util.CollectAxioms

/-! Direct descent-coordinate checks on the unchanged original germ tuples. -/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
@[expose] public noncomputable section
open CategoryTheory
open Opposite
open AlgebraicGeometry
open Motivic
open _root_.Motivic.PresheafWithTransfers
universe u w
namespace MotivicTest.OriginalGermTupleCoverComparison
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))
set_option quotPrecheck false in
local notation "G" => ((toPresheaf k).obj (originalGermTuplePresheaf k P hP))

/-- The literal categorical matching condition supplies the coordinate comparison
at arbitrary scheme points and for an arbitrary-index family. -/
theorem actual_matching_coordinate
    {I : Type w} {X : SmoothSite (Spec (.of k))}
    (V : I → SmoothSite (Spec (.of k))) (q : ∀ i, V i ⟶ X)
    (hq : ∀ i, Etale (q i).left)
    (s : ∀ i, originalGermTuples k P (Cor.mk (V i)))
    (hs : Presieve.Arrows.Compatible ((G) ⋙ forget AddCommGrpCat) q s)
    (t : originalGermTuples k P (Cor.mk X))
    (i : I) (x : (V i).left) [IsIso ((q i).left.residueFieldMap x)]
    (hx : ((G).map (q i).op t) x = s i x)
    (j : I) (y : (V j).left) (hy : (q j).left y = (q i).left x) :
    ((G).map (q j).op t) y = s j y :=
  originalGermTuple_coordinate_eq_of_matching k P hP V q hq s hs t i x hx j y hy

/-- The graph formula used in the comparison is the original fiber map, not a
new action imposed on replacement stalks. -/
theorem actual_original_restriction {X Y : SmoothSite (Spec (.of k))}
    (f : X ⟶ Y) (t : originalGermTuples k P (Cor.mk Y)) (x : X.left) :
    ((G).map f.op t) x =
      SmoothSite.originalGermPullback.{u, 0} ((toPresheaf k).obj P) f x (t (f.left x)) :=
  originalGermTuplePresheaf_map_apply k P hP f t x

open Lean in
run_cmd do
  for name in #[``actual_matching_coordinate, ``actual_original_restriction,
      ``originalGermTuple_coordinate_eq_of_matching,
      ``originalGermTuplePresheaf_map_apply] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual matching-cover coordinate comparison: standard foundations only."

end MotivicTest.OriginalGermTupleCoverComparison
