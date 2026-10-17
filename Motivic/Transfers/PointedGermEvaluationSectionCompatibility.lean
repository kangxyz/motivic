/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.PointedGermEvaluationAdditivity
public import Motivic.Transfers.PointedGermLiftSections

/-! # Actual generator germ evaluation agrees with transfer of global sections -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.PresheafWithTransfers
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))
  {X Y : SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)
include hP

/-- On a tuple of original germs of one actual section, the choice-independent
generator evaluation is the original transfer followed by the original germ map. -/
theorem generatorGermEvaluation_section
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left)
    (s : P.sections (Cor.mk Y)) :
    generatorGermEvaluation k P A x
        (fun y => SmoothSite.sectionToNisnevichPoint.{u, 0} F Y y s) =
      SmoothSite.sectionToNisnevichPoint.{u, 0} F X x (P.transfer A.cycle s) := by
  let a := fun y => SmoothSite.sectionToNisnevichPoint.{u, 0} F Y y s
  obtain ⟨L⟩ := exists_pointedGermLiftWitness k P A x a
  let M : PointedGermLiftWitness k P (show Cor.mk X ⟶ Cor.mk Y from A.cycle) x a :=
    { L with
      representative := fun i => (F).map (L.target i).toBase.op s
      represents := fun i => ConcreteCategory.congr_hom
        (SmoothSite.restriction_sectionToNisnevichPoint.{u, 0} F (L.target i)) s }
  rw [generatorGermEvaluation_eq_of_witness k P hP A x a M]
  exact M.value_eq_transfer_of_restrictions k P s (fun _ => rfl)

end Motivic.PresheafWithTransfers
