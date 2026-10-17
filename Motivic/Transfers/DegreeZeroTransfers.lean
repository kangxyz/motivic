/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.DegreeZeroCohomology

/-!
# Signed transfers on actual degree-zero ordinary cohomology

The groups are the actual ordinary Ext-based Nisnevich cohomology groups.
Their signed transfer action is transported along the canonical section
comparison. Restriction along every actual graph agrees with the original
cohomology presheaf map. No positive-degree transfer structure is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite

universe w u

namespace Motivic.SheafWithTransfers

variable {k : Type u} [Field k]
variable [HasExt.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The canonical degree-zero comparison, with the complete original transfer sections. -/
def degreeZeroSectionsEquiv (F : SheafWithTransfers.{u + 1} k) (X : Cor k) :
    SheafCohomology.H.{w, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((toSheaf.{u + 1} k).obj F) 0 X.toSmoothSite ≃+
      PresheafWithTransfers.sections F.obj X :=
  SheafCohomology.zeroSections.{w, u + 1} _ _ _

/-- The action of an actual signed finite correspondence on actual ordinary `H⁰`. -/
def degreeZeroTransfer (F : SheafWithTransfers.{u + 1} k) {X Y : Cor k} (α : X ⟶ Y) :
    SheafCohomology.H.{w, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((toSheaf.{u + 1} k).obj F) 0 Y.toSmoothSite ⟶
      SheafCohomology.H.{w, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((toSheaf.{u + 1} k).obj F) 0 X.toSmoothSite :=
  AddCommGrpCat.ofHom
    ((degreeZeroSectionsEquiv F X).symm.toAddMonoidHom.comp
      ((PresheafWithTransfers.transfer F.obj α).hom.comp
        (degreeZeroSectionsEquiv F Y).toAddMonoidHom))

@[simp]
theorem degreeZeroSectionsEquiv_transfer (F : SheafWithTransfers.{u + 1} k)
    {X Y : Cor k} (α : X ⟶ Y)
    (x : SheafCohomology.H.{w, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toSheaf.{u + 1} k).obj F) 0 Y.toSmoothSite) :
    degreeZeroSectionsEquiv F X (degreeZeroTransfer F α x) =
      PresheafWithTransfers.transfer F.obj α (degreeZeroSectionsEquiv F Y x) :=
  (degreeZeroSectionsEquiv F X).apply_symm_apply _

@[simp]
theorem degreeZeroTransfer_id (F : SheafWithTransfers.{u + 1} k) (X : Cor k) :
    degreeZeroTransfer F (𝟙 X) = 𝟙 _ := by
  ext x
  apply (degreeZeroSectionsEquiv F X).injective
  simp

@[simp]
theorem degreeZeroTransfer_comp (F : SheafWithTransfers.{u + 1} k)
    {X Y Z : Cor k} (α : X ⟶ Y) (β : Y ⟶ Z) :
    degreeZeroTransfer F (α ≫ β) = degreeZeroTransfer F β ≫ degreeZeroTransfer F α := by
  ext x
  apply (degreeZeroSectionsEquiv F X).injective
  simp

@[simp]
theorem degreeZeroTransfer_add (F : SheafWithTransfers.{u + 1} k)
    {X Y : Cor k} (α β : X ⟶ Y) :
    degreeZeroTransfer F (α + β) = degreeZeroTransfer F α + degreeZeroTransfer F β := by
  ext x
  apply (degreeZeroSectionsEquiv F X).injective
  simp

/-- Graph transfers agree with the actual ordinary cohomology restriction. -/
theorem degreeZeroTransfer_graph (F : SheafWithTransfers.{u + 1} k)
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    degreeZeroTransfer F ((Cor.graphFunctor k).map f) =
      (SheafCohomology.presheaf.{w, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((toSheaf.{u + 1} k).obj F) 0).map f.op := by
  ext x
  apply (degreeZeroSectionsEquiv F ((Cor.graphFunctor k).obj X)).injective
  exact (degreeZeroSectionsEquiv_transfer F ((Cor.graphFunctor k).map f) x).trans
    (SheafCohomology.zeroSections_restriction.{w, u + 1} _
      ((toSheaf.{u + 1} k).obj F) f x).symm

/-- Actual degree-zero ordinary cohomology, with its complete signed transfers. -/
def degreeZeroPresheafWithTransfers (F : SheafWithTransfers.{u + 1} k) :
    PresheafWithTransfers.{w} k :=
  ⟨{ obj X := SheafCohomology.H.{w, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((toSheaf.{u + 1} k).obj F) 0 X.unop.toSmoothSite
     map f := degreeZeroTransfer F f.unop
     map_id X := degreeZeroTransfer_id F X.unop
     map_comp f g := degreeZeroTransfer_comp F g.unop f.unop },
   { map_add := degreeZeroTransfer_add F _ _ }⟩

/-- Forgetting the constructed transfers recovers the actual ordinary cohomology presheaf. -/
def degreeZeroUnderlyingIso (F : SheafWithTransfers.{u + 1} k) :
    (PresheafWithTransfers.toPresheaf k).obj (degreeZeroPresheafWithTransfers F) ≅
      SheafCohomology.presheaf.{w, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((toSheaf.{u + 1} k).obj F) 0 :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun f => by
      change degreeZeroTransfer F ((Cor.graphFunctor k).map f.unop) ≫ 𝟙 _ =
        𝟙 _ ≫ (SheafCohomology.presheaf.{w, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((toSheaf.{u + 1} k).obj F) 0).map f
      rw [Category.comp_id, Category.id_comp]
      exact degreeZeroTransfer_graph F f.unop)

end Motivic.SheafWithTransfers
