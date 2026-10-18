/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.BoundaryFramed
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local

/-!
# Tensor compatibility for boundary-framed classes

The native tensor pullback comparison transports the specified frames. The
normalized section-pair equation identifies the resulting framed objects while
retaining the original sections and the original line bundle.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible.BoundaryFramedLineBundle

variable {C D : Scheme.{u}} {i : D ⟶ C}

/-- Tensor the original line bundles and their specified boundary frames. -/
def tensor (L M : BoundaryFramedLineBundle i) : BoundaryFramedLineBundle i where
  lineBundle := tensorLineBundle C L.lineBundle M.lineBundle
  frame := PullbackTensor.Local.pullbackLineBundleTensorIso i L.lineBundle M.lineBundle ≪≫
    tensorSheafIso D L.frame M.frame ≪≫
      tensorSheafLeftUnit D (SheafOfModules.unit D.ringCatSheaf)

/-- The tensor frame uses the canonical pullback map and the two original frames. -/
theorem tensor_frame_hom (L M : BoundaryFramedLineBundle i) :
    (tensor L M).frame.hom =
      pullbackTensorMap i L.lineBundle.val M.lineBundle.val ≫
        tensorSheafMap D L.frame.hom M.frame.hom ≫
          (tensorSheafLeftUnit D (SheafOfModules.unit D.ringCatSheaf)).hom := rfl

/-- Tensor preserves frame-preserving isomorphisms through the native tensor map. -/
def Iso.tensor {L L' M M' : BoundaryFramedLineBundle i}
    (e : Iso L L') (f : Iso M M') : Iso (tensor L M) (tensor L' M') where
  iso := tensorSheafIso C e.iso f.iso
  frame_hom := by
    change (Modules.pullback i).map (tensorSheafMap C e.iso.hom f.iso.hom) ≫
      (BoundaryFramedLineBundle.tensor L' M').frame.hom =
        (BoundaryFramedLineBundle.tensor L M).frame.hom
    rw [tensor_frame_hom, tensor_frame_hom]
    rw [← Category.assoc, ← Category.assoc, pullbackTensorMap_naturality]
    simp only [Category.assoc]
    rw [tensorSheafMap_comp_assoc, e.frame_hom, f.frame_hom]

/-- Tensor on boundary-framed isomorphism classes. -/
def tensorClass (a b : Class i) : Class i :=
  Quotient.liftOn₂ a b (fun L M => classOf (tensor L M)) (by
    intro L L' M M' ⟨e⟩ ⟨f⟩
    exact Quotient.sound ⟨e.tensor f⟩)

@[simp]
theorem tensorClass_classOf (L M : BoundaryFramedLineBundle i) :
    tensorClass (classOf L) (classOf M) = classOf (tensor L M) := rfl

/-- Forgetting the frames recovers addition in the original ordinary Picard group. -/
theorem forget_tensorClass (a b : Class i) :
    forget (tensorClass a b) = forget a + forget b := by
  induction a using Quotient.inductionOn with | h L =>
    induction b using Quotient.inductionOn with | h M => rfl

/-- The normalized boundary equation is an equality of the actual inverse frames. -/
theorem ofSection_frame_inv_eq_tensor (T : LineBundle C) (M : BoundaryFramedLineBundle i)
    (s : SheafOfModules.unit C.ringCatSheaf ⟶ (tensorLineBundle C T M.lineBundle).val)
    (t : SheafOfModules.unit C.ringCatSheaf ⟶ T.val)
    [IsIso (pullbackSectionMap i s)] [IsIso (pullbackSectionMap i t)]
    (h : pullbackSectionMap i s ≫ pullbackTensorMap i T.val M.lineBundle.val =
      tensorUnitSection (pullbackSectionMap i t) M.frame.inv) :
    (ofSection i (tensorLineBundle C T M.lineBundle) s).frame.inv =
      (tensor (ofSection i T t) M).frame.inv := by
  have : IsIso (pullbackTensorMap i T.val M.lineBundle.val) :=
    PullbackTensor.Local.pullbackTensorMap_isIso i T.val M.lineBundle.val T.property
  apply (cancel_mono (pullbackTensorMap i T.val M.lineBundle.val)).mp
  rw [ofSection_frame_inv, h]
  change tensorUnitSection (pullbackSectionMap i t) M.frame.inv =
    (tensorSheafLeftUnit D (SheafOfModules.unit D.ringCatSheaf)).inv ≫
      tensorSheafMap D (pullbackSectionMap i t) M.frame.inv ≫
        (PullbackTensor.Local.pullbackLineBundleTensorIso i T M.lineBundle).inv ≫
          (PullbackTensor.Local.pullbackLineBundleTensorIso i T M.lineBundle).hom
  simp only [CategoryTheory.Iso.inv_hom_id,
    Category.comp_id, tensorUnitSection]

/-- The same normalized sections identify the framed numerator with the tensor of
its denominator and the prescribed framed line bundle. -/
def normalizedSectionIso (T : LineBundle C) (M : BoundaryFramedLineBundle i)
    (s : SheafOfModules.unit C.ringCatSheaf ⟶ (tensorLineBundle C T M.lineBundle).val)
    (t : SheafOfModules.unit C.ringCatSheaf ⟶ T.val)
    [IsIso (pullbackSectionMap i s)] [IsIso (pullbackSectionMap i t)]
    (h : pullbackSectionMap i s ≫ pullbackTensorMap i T.val M.lineBundle.val =
      tensorUnitSection (pullbackSectionMap i t) M.frame.inv) :
    Iso (ofSection i (tensorLineBundle C T M.lineBundle) s) (tensor (ofSection i T t) M) where
  iso := CategoryTheory.Iso.refl _
  frame_hom := by
    change (Modules.pullback i).map (𝟙 (tensorLineBundle C T M.lineBundle).val) ≫
      (tensor (ofSection i T t) M).frame.hom =
        (ofSection i (tensorLineBundle C T M.lineBundle) s).frame.hom
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    have he := ofSection_frame_inv_eq_tensor T M s t h
    apply (cancel_epi (ofSection i (tensorLineBundle C T M.lineBundle) s).frame.inv).mp
    rw [CategoryTheory.Iso.inv_hom_id, he, CategoryTheory.Iso.inv_hom_id]

/-- The actual normalized pair has the specified boundary-framed tensor class. -/
theorem classOf_normalizedSection (T : LineBundle C) (M : BoundaryFramedLineBundle i)
    (s : SheafOfModules.unit C.ringCatSheaf ⟶ (tensorLineBundle C T M.lineBundle).val)
    (t : SheafOfModules.unit C.ringCatSheaf ⟶ T.val)
    [IsIso (pullbackSectionMap i s)] [IsIso (pullbackSectionMap i t)]
    (h : pullbackSectionMap i s ≫ pullbackTensorMap i T.val M.lineBundle.val =
      tensorUnitSection (pullbackSectionMap i t) M.frame.inv) :
    classOf (ofSection i (tensorLineBundle C T M.lineBundle) s) =
      tensorClass (classOf (ofSection i T t)) (classOf M) :=
  Quotient.sound ⟨normalizedSectionIso T M s t h⟩

end AlgebraicGeometry.Scheme.Modules.Invertible.BoundaryFramedLineBundle
