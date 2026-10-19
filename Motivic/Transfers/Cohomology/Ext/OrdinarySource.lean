/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.UnderlyingExactness
public import Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.DegreeZero
public import Motivic.Transfers.Presheaf.ReducedTorus
public import Motivic.Aglib.CategoryTheory.LiftedAdditiveYoneda

/-! # The actual ordinary-to-transfer section source

The transfer source is the genuine Nisnevich sheafification of the lifted signed
representable. The ordinary source is the unchanged free abelian section source.
The comparison map represents the sheafified identity correspondence.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf
variable (k : Type u) [Field k]

/-- The actual signed representable, sheafified with its original transfers. -/
def transferRepresentable : Cor k ⥤ SheafWithTransfers.{u + 1} k :=
  PresheafWithTransfers.representableLarge k ⋙ PresheafWithTransfers.nisnevichSheafify k

instance transferRepresentable_additive : (transferRepresentable k).Additive := by
  have : (PresheafWithTransfers.representableLarge k).Additive := ⟨by
    intro X Y f g
    ext Z a
    change ULift.up (a.down ≫ (f + g)) =
      ULift.up (a.down ≫ f + a.down ≫ g)
    rw [Preadditive.comp_add]⟩
  unfold transferRepresentable
  infer_instance

/-- Transfer Yoneda followed by the genuine sheafification adjunction represents sections. -/
def transferSectionsEquiv (X : Cor k) (F : SheafWithTransfers.{u + 1} k) :
    ((transferRepresentable k).obj X ⟶ F) ≃+
      PresheafWithTransfers.sections F.obj X :=
  { toEquiv := (PresheafWithTransfers.nisnevichSheafificationHomEquiv k
      ((PresheafWithTransfers.representableLarge k).obj X) F).trans
        (AdditiveFunctor.liftedYonedaAddEquiv F.obj X).toEquiv
    map_add' _ _ := by rfl }

/-- The section is evaluation of the original sheafification unit on the identity cycle. -/
theorem transferSectionsEquiv_apply (X : Cor k) (F : SheafWithTransfers.{u + 1} k)
    (f : (transferRepresentable k).obj X ⟶ F) :
    transferSectionsEquiv k X F f =
      f.hom.hom.app (op X)
        ((PresheafWithTransfers.toNisnevichSheafify k
          ((PresheafWithTransfers.representableLarge k).obj X)).hom.app (op X)
            (ULift.up (𝟙 X))) := rfl

/-- Evaluation commutes with the actual coefficient morphism. -/
theorem transferSectionsEquiv_comp (X : Cor k) {F G : SheafWithTransfers.{u + 1} k}
    (f : (transferRepresentable k).obj X ⟶ F) (g : F ⟶ G) :
    transferSectionsEquiv k X G (f ≫ g) =
      g.hom.hom.app (op X) (transferSectionsEquiv k X F f) := rfl

/-- Lifted Yoneda is contravariant for the original signed correspondence map. -/
private theorem liftedYoneda_naturality_left
    (P : PresheafWithTransfers.{u + 1} k) {X Y : Cor k} (a : X ⟶ Y)
    (f : (PresheafWithTransfers.representableLarge k).obj Y ⟶ P) :
    AdditiveFunctor.liftedYonedaAddEquiv P X
        ((PresheafWithTransfers.representableLarge k).map a ≫ f) =
      P.obj.map a.op (AdditiveFunctor.liftedYonedaAddEquiv P Y f) := by
  change f.hom.app (op X) (ULift.up ((𝟙 X) ≫ a)) =
    P.obj.map a.op (f.hom.app (op Y) (ULift.up (𝟙 Y)))
  rw [Category.id_comp]
  have h := ConcreteCategory.congr_hom (f.hom.naturality a.op) (ULift.up (𝟙 Y))
  change f.hom.app (op X) (ULift.up (a ≫ 𝟙 Y)) =
    P.obj.map a.op (f.hom.app (op Y) (ULift.up (𝟙 Y))) at h
  simpa only [Category.comp_id] using h

/-- The sheafified section equivalence retains naturality for every signed correspondence. -/
theorem transferSectionsEquiv_naturality_left (F : SheafWithTransfers.{u + 1} k)
    {X Y : Cor k} (a : X ⟶ Y) (f : (transferRepresentable k).obj Y ⟶ F) :
    transferSectionsEquiv k X F ((transferRepresentable k).map a ≫ f) =
      PresheafWithTransfers.transfer F.obj a (transferSectionsEquiv k Y F f) := by
  change AdditiveFunctor.liftedYonedaAddEquiv F.obj X
    (((PresheafWithTransfers.nisnevichSheafificationAdjunction k).homEquiv _ _)
      ((PresheafWithTransfers.nisnevichSheafify k).map
        ((PresheafWithTransfers.representableLarge k).map a) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact liftedYoneda_naturality_left k F.obj a _

/-- The corresponding ordinary Hom equivalence retains the original section source. -/
def ordinaryTransferHomEquiv (X : SmoothSite (Spec (.of k)))
    (F : SheafWithTransfers.{u + 1} k) :
    ((transferRepresentable k).obj (Cor.mk X) ⟶ F) ≃+
      (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) X ⟶ (toSheaf k).obj F) :=
  (transferSectionsEquiv k (Cor.mk X) F).trans
    (Hypercohomology.sectionsAddEquiv.{u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) X ((toSheaf k).obj F)).symm

/-- The ordinary source maps to the underlying sheaf of the actual transfer source. -/
def ordinaryToTransferSource (X : SmoothSite (Spec (.of k))) :
    Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) X ⟶
        (toSheaf k).obj ((transferRepresentable k).obj (Cor.mk X)) :=
  ordinaryTransferHomEquiv k X _ (𝟙 _)

/-- Evaluation of the Hom equivalence is the original transfer section. -/
theorem ordinaryTransferHomEquiv_sections (X : SmoothSite (Spec (.of k)))
    (F : SheafWithTransfers.{u + 1} k)
    (f : (transferRepresentable k).obj (Cor.mk X) ⟶ F) :
    Hypercohomology.sectionsAddEquiv.{u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) X ((toSheaf k).obj F)
        (ordinaryTransferHomEquiv k X F f) = transferSectionsEquiv k (Cor.mk X) F f :=
  (Hypercohomology.sectionsAddEquiv.{u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) X ((toSheaf k).obj F)).apply_symm_apply _

/-- The Hom equivalence is exactly precomposition with the specified source map
following the genuine forgetful functor, not a different abstract bijection. -/
theorem ordinaryTransferHomEquiv_apply (X : SmoothSite (Spec (.of k)))
    (F : SheafWithTransfers.{u + 1} k)
    (f : (transferRepresentable k).obj (Cor.mk X) ⟶ F) :
    ordinaryTransferHomEquiv k X F f = ordinaryToTransferSource k X ≫ (toSheaf k).map f := by
  apply (Hypercohomology.sectionsAddEquiv.{u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) X ((toSheaf k).obj F)).injective
  have h := Hypercohomology.sectionsEquiv_naturality
    (SmoothSite.nisnevichTopology (Spec (.of k))) X
    (ordinaryToTransferSource k X) ((toSheaf k).map f)
  change (Hypercohomology.sectionsAddEquiv.{u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) X ((toSheaf k).obj F))
      (ordinaryToTransferSource k X ≫ (toSheaf k).map f) = _ at h
  rw [ordinaryTransferHomEquiv_sections, h]
  change transferSectionsEquiv k (Cor.mk X) F f =
    f.hom.hom.app (op (Cor.mk X))
      (Hypercohomology.sectionsAddEquiv.{u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) X
        ((toSheaf k).obj ((transferRepresentable k).obj (Cor.mk X)))
          (ordinaryTransferHomEquiv k X _ (𝟙 _)))
  rw [ordinaryTransferHomEquiv_sections]
  simpa only [Category.id_comp] using
    transferSectionsEquiv_comp k (Cor.mk X) (𝟙 _) f

/-- The specified source map commutes with every actual smooth-site graph restriction. -/
theorem ordinaryToTransferSource_naturality
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    (Hypercohomology.freeAbelianSheafFunctor.{u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))).map f ≫
        ordinaryToTransferSource k Y =
      ordinaryToTransferSource k X ≫
        (toSheaf k).map ((transferRepresentable k).map ((Cor.graphFunctor k).map f)) := by
  let R := (transferRepresentable k).obj (Cor.mk Y)
  apply (Hypercohomology.sectionsAddEquiv.{u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) X ((toSheaf k).obj R)).injective
  rw [Hypercohomology.sectionsAddEquiv_naturality_left]
  let a : Cor.mk X ⟶ Cor.mk Y := (Cor.graphFunctor k).map f
  let r : (transferRepresentable k).obj (Cor.mk X) ⟶ R :=
    (transferRepresentable k).map a
  rw [← ordinaryTransferHomEquiv_apply k X R r,
    ordinaryTransferHomEquiv_sections]
  change PresheafWithTransfers.transfer R.obj ((Cor.graphFunctor k).map f)
      (Hypercohomology.sectionsAddEquiv.{u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) Y ((toSheaf k).obj R)
          (ordinaryTransferHomEquiv k Y R (𝟙 R))) = _
  rw [ordinaryTransferHomEquiv_sections]
  have h := (transferSectionsEquiv_naturality_left k R a (𝟙 R)).symm
  change PresheafWithTransfers.transfer R.obj a
      (transferSectionsEquiv k (Cor.mk Y) R (𝟙 R)) =
    transferSectionsEquiv k (Cor.mk X) R (r ≫ 𝟙 R) at h
  rw [Category.comp_id] at h
  exact h

end Motivic.SheafWithTransfers
