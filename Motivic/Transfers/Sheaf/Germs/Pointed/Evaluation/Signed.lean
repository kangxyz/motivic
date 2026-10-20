/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Pointed.Evaluation.SectionCompatibility
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! # Signed correspondence evaluation on the original Nisnevich point fibers

This is the additive extension of the geometrically constructed generator action.
Composition is not assumed in this construction.
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
  {X Y : SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)

/-- Signed extension in the correspondence variable, still valued in the original
point-fiber groups. -/
def correspondenceGermHom (x : X.left) :
    (Cor.mk X ⟶ Cor.mk Y) →+
      ((∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) →+
        (SmoothSite.nisnevichPointFiberCocone X x F).pt) :=
  Finsupp.liftAddHom (fun A => zmultiplesHom _ (generatorGermHom k P hP A x))

theorem correspondenceGermHom_cycle
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left) :
    correspondenceGermHom k P hP x A.cycle = generatorGermHom k P hP A x := by
  classical
  change (Finsupp.single A (1 : ℤ)).sum
    (fun B m => m • generatorGermHom k P hP B x) = _
  rw [Finsupp.sum_single_index (zero_zsmul _), one_zsmul]

@[simp] theorem correspondenceGermHom_cycle_simp
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left) :
    @DFunLike.coe
      ((Cor.mk X ⟶ Cor.mk Y) →+
        ((∀ y : Y.left, ((Y.nisnevichPoint y).presheafFiber (A := AddCommGrpCat.{u + 1})).obj F) →+
          ((X.nisnevichPoint x).presheafFiber (A := AddCommGrpCat.{u + 1})).obj F))
      _ _ _ (correspondenceGermHom k P hP x) A.cycle = generatorGermHom k P hP A x :=
  correspondenceGermHom_cycle k P hP A x

/-- The signed evaluation is computed by the actual integer coefficients of the
original finite correspondence. -/
theorem correspondenceGermHom_apply
    (δ : Cor.mk X ⟶ Cor.mk Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) :
    correspondenceGermHom k P hP x δ a =
      ∑ A ∈ δ.support,
        (show FiniteCorrespondence X.hom Y.hom from δ) A •
          generatorGermEvaluation k P A x a := by
  classical
  change ((show FiniteCorrespondence X.hom Y.hom from δ).sum
    (fun A m => m • generatorGermHom k P hP A x)) a = _
  simp only [Finsupp.sum, AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply]
  rfl

/-- On genuine global sections the signed extension recovers the original
presheaf-with-transfers action followed by the original germ map. -/
theorem correspondenceGermHom_section
    (δ : Cor.mk X ⟶ Cor.mk Y) (x : X.left) (s : P.sections (Cor.mk Y)) :
    correspondenceGermHom k P hP x δ
        (fun y => SmoothSite.sectionToNisnevichPoint.{u, 0} F Y y s) =
      SmoothSite.sectionToNisnevichPoint.{u, 0} F X x (P.transfer δ s) := by
  classical
  let a := fun y => SmoothSite.sectionToNisnevichPoint.{u, 0} F Y y s
  let e : (Cor.mk X ⟶ Cor.mk Y) →+ P.sections (Cor.mk X) :=
    { toFun := fun γ => P.transfer γ s
      map_zero' := by simp
      map_add' := fun γ η => by simp only [transfer_add, AddCommGrpCat.hom_add_apply] }
  have hsingle (A : FiniteCorrespondenceGenerator X.hom Y.hom) (m : ℤ) :
      correspondenceGermHom k P hP x (Finsupp.single A m) a =
        SmoothSite.sectionToNisnevichPoint.{u, 0} F X x (e (Finsupp.single A m)) := by
    have hm : Finsupp.single A m = m • A.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle, Finsupp.smul_single]
    rw [hm, map_zsmul, AddMonoidHom.zsmul_apply, correspondenceGermHom_cycle,
      map_zsmul, map_zsmul]
    exact congrArg (fun b => m • b) (generatorGermEvaluation_section k P hP A x s)
  change correspondenceGermHom k P hP x δ a =
    SmoothSite.sectionToNisnevichPoint.{u, 0} F X x (e δ)
  induction δ using Finsupp.induction_linear with
  | zero => rw [map_zero, AddMonoidHom.zero_apply, map_zero, map_zero]
  | add γ η hγ hη =>
    simp only [map_add, AddMonoidHom.add_apply, hγ, hη]
  | single A m => exact hsingle A m

end Motivic.PresheafWithTransfers
