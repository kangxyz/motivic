/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Pointed.Evaluation.Composition

/-! # The actual original-germ tuple presheaf with signed transfers

The groups are literally products of the original Nisnevich point fibers.
This module asserts neither sheafness nor cohomological acyclicity of this presheaf.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite AlgebraicGeometry
universe u
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)

/-- The original germ tuple group at a smooth object. -/
def originalGermTuples (X : Cor k) : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of (∀ x : X.toSmoothSite.left,
    (SmoothSite.nisnevichPointFiberCocone X.toSmoothSite x F).pt)

/-- Actual signed transfer on all source-point coordinates. -/
def originalGermTupleTransfer {X Y : Cor k} (δ : X ⟶ Y) :
    originalGermTuples k P Y ⟶ originalGermTuples k P X :=
  AddCommGrpCat.ofHom
    { toFun := fun a x => correspondenceGermHom k P hP x δ a
      map_zero' := by funext x; exact map_zero (correspondenceGermHom k P hP x δ)
      map_add' := fun a b => by funext x; exact map_add (correspondenceGermHom k P hP x δ) a b }

/-- The original tuple groups carry the proved contravariant signed action. -/
def originalGermTuplePresheaf : PresheafWithTransfers.{u + 1} k :=
  ⟨{ obj X := originalGermTuples k P X.unop
     map f := originalGermTupleTransfer k P hP f.unop
     map_id X := by
       ext a
       funext x
       exact correspondenceGermHom_id k P hP x a
     map_comp f g := by
       ext a
       funext x
       exact correspondenceGermHom_comp k P hP g.unop f.unop x a },
    { map_add := by
        intro X Y f g
        ext a
        funext x
        exact congrArg (fun e => e a) (map_add (correspondenceGermHom k P hP x) f.unop g.unop) }⟩

/-- Original global sections map to their literal tuples of original germs. -/
def toOriginalGermTuplePresheaf : P ⟶ originalGermTuplePresheaf k P hP :=
  ⟨{ app X := AddCommGrpCat.ofHom
        { toFun := fun s x => SmoothSite.sectionToNisnevichPoint.{u, 0} F X.unop.toSmoothSite x s
          map_zero' := by funext x; exact map_zero _
          map_add' := fun s t => by funext x; exact map_add _ s t }
     naturality := by
       intro X Y f
       ext s
       funext x
       exact (correspondenceGermHom_section k P hP f.unop x s).symm }⟩

/-- The graph action remains the canonical map of the original fiber colimits. -/
theorem originalGermTupleTransfer_graph {X Y : SmoothSite (Spec (.of k))}
    (f : X ⟶ Y) (a : originalGermTuples k P (Cor.mk Y)) (x : X.left) :
    originalGermTupleTransfer k P hP ((Cor.graphFunctor k).map f) a x =
      SmoothSite.originalGermPullback.{u, 0} F f x (a (f.left x)) :=
  correspondenceGermHom_graph k P hP f x a

end Motivic.PresheafWithTransfers
