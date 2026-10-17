/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OrdinaryTransferExtComparison
public import Motivic.Transfers.TransferExtPresheaf

/-! # Actual transfers on the original ordinary Nisnevich cohomology groups -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite
universe w w' u
namespace Motivic.SheafWithTransfers
variable (k : Type u) [Field k]
  [HasExt.{w} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{w'} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (F : SheafWithTransfers.{u + 1} k) (n : ℕ)

/-- The action is transported into the literal original ordinary cohomology groups.
The two Ext universes need not coincide. -/
def ordinaryCohomologyPresheafCor : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{w'} :=
  { obj X := SheafCohomology.H.{w', u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) n X.unop.toSmoothSite
    map {X Y} f := AddCommGrpCat.ofHom
       ((transferExtEquiv.{w, w', u} k Y.unop.toSmoothSite F n).toAddMonoidHom.comp
         (((transferExtPresheaf.{w, u} k F n).map f).hom.comp
           (transferExtEquiv.{w, w', u} k X.unop.toSmoothSite F n).symm.toAddMonoidHom))
    map_id X := by
       ext a
       change transferExtEquiv.{w, w', u} k X.unop.toSmoothSite F n
         ((transferExtPresheaf.{w, u} k F n).map (𝟙 X)
           ((transferExtEquiv.{w, w', u} k X.unop.toSmoothSite F n).symm a)) = a
       rw [(transferExtPresheaf.{w, u} k F n).map_id]
       exact AddEquiv.apply_symm_apply _ a
    map_comp {X Y Z} f g := by
       ext a
       change transferExtEquiv.{w, w', u} k Z.unop.toSmoothSite F n
         ((transferExtPresheaf.{w, u} k F n).map (f ≫ g)
           ((transferExtEquiv.{w, w', u} k X.unop.toSmoothSite F n).symm a)) =
         transferExtEquiv.{w, w', u} k Z.unop.toSmoothSite F n
           ((transferExtPresheaf.{w, u} k F n).map g
             ((transferExtEquiv.{w, w', u} k Y.unop.toSmoothSite F n).symm
               (transferExtEquiv.{w, w', u} k Y.unop.toSmoothSite F n
                 ((transferExtPresheaf.{w, u} k F n).map f
                   ((transferExtEquiv.{w, w', u} k X.unop.toSmoothSite F n).symm a)))))
       rw [AddEquiv.symm_apply_apply, (transferExtPresheaf.{w, u} k F n).map_comp]
       rfl }

instance ordinaryCohomologyPresheafCor_additive :
    (ordinaryCohomologyPresheafCor.{w, w', u} k F n).Additive where
  map_add := by
        intro X Y f g
        ext a
        change transferExtEquiv.{w, w', u} k Y.unop.toSmoothSite F n
          ((transferExtPresheaf.{w, u} k F n).map (f + g)
            ((transferExtEquiv.{w, w', u} k X.unop.toSmoothSite F n).symm a)) = _
        rw [(transferExtPresheaf.{w, u} k F n).map_add]
        exact map_add _ _ _

/-- The actual original cohomology groups, bundled with all signed transfers. -/
def ordinaryCohomologyTransfers : PresheafWithTransfers.{w'} k :=
  ⟨ordinaryCohomologyPresheafCor.{w, w', u} k F n, by
    change (ordinaryCohomologyPresheafCor.{w, w', u} k F n).Additive
    infer_instance⟩

/-- Signed transfers are transported by the proved comparison, without changing their groups. -/
theorem ordinaryCohomologyTransfers_apply {X Y : Cor k} (a : X ⟶ Y)
    (e : Ext.{w} ((transferRepresentable k).obj Y) F n) :
    (ordinaryCohomologyTransfers.{w, w', u} k F n).transfer a
        (transferExtEquiv.{w, w', u} k Y.toSmoothSite F n e) =
      transferExtEquiv.{w, w', u} k X.toSmoothSite F n
        ((transferExtPresheaf.{w, u} k F n).map a.op e) := by
  change transferExtEquiv.{w, w', u} k X.toSmoothSite F n
    ((transferExtPresheaf.{w, u} k F n).map a.op
      ((transferExtEquiv.{w, w', u} k Y.toSmoothSite F n).symm
        (transferExtEquiv.{w, w', u} k Y.toSmoothSite F n e))) = _
  rw [AddEquiv.symm_apply_apply]

/-- A graph correspondence acts by the literal original ordinary restriction map. -/
theorem ordinaryCohomologyTransfers_graph {X Y : SmoothSite (Spec (.of k))}
    (f : X ⟶ Y)
    (e : SheafCohomology.H.{w', u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) n Y) :
    (ordinaryCohomologyTransfers.{w, w', u} k F n).transfer ((Cor.graphFunctor k).map f) e =
      (SheafCohomology.presheaf.{w', u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) n).map f.op e := by
  obtain ⟨a, rfl⟩ := (transferExtEquiv.{w, w', u} k Y F n).surjective e
  exact (ordinaryCohomologyTransfers_apply.{w, w', u} k F n
    ((Cor.graphFunctor k).map f) a).trans
      (transferExtEquiv_naturality_graph k f F n a)

/-- Graph restriction recovers the original ordinary cohomology presheaf on the nose in groups. -/
def ordinaryCohomologyTransfersGraphIso :
    (PresheafWithTransfers.toPresheaf k).obj (ordinaryCohomologyTransfers.{w, w', u} k F n) ≅
      SheafCohomology.presheaf.{w', u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) n :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    ext e
    exact ordinaryCohomologyTransfers_graph k F n f.unop e)

/-- The original ordinary coefficient map agrees with coefficient transport in transfer Ext. -/
theorem ordinaryCoefficient_transferExtEquiv {F G : SheafWithTransfers.{u + 1} k}
    (a : F ⟶ G) (X : Cor k)
    (e : Ext.{w} ((transferRepresentable k).obj X) F n) :
    ((SheafCohomology.presheafFunctor.{w', u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) n).map ((toSheaf k).map a)).app
        (op X.toSmoothSite) (transferExtEquiv.{w, w', u} k X.toSmoothSite F n e) =
      transferExtEquiv.{w, w', u} k X.toSmoothSite G n
        ((transferExtCoefficientMap.{w, u} k n a).app (op X) e) :=
  (transferExtEquiv_naturality_coeff k X.toSmoothSite a n e).symm

/-- Actual ordinary cohomology coefficient maps preserve every signed transfer. -/
def ordinaryCohomologyTransfersMap {F G : SheafWithTransfers.{u + 1} k} (a : F ⟶ G) :
    ordinaryCohomologyTransfers.{w, w', u} k F n ⟶ ordinaryCohomologyTransfers.{w, w', u} k G n :=
  ObjectProperty.homMk
    { app := fun X ↦ ((SheafCohomology.presheafFunctor.{w', u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) n).map ((toSheaf k).map a)).app
          (op X.unop.toSmoothSite)
      naturality := by
        intro X Y f
        ext s
        obtain ⟨e, rfl⟩ := (transferExtEquiv.{w, w', u} k X.unop.toSmoothSite F n).surjective s
        change ((SheafCohomology.presheafFunctor.{w', u + 1, u, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k))) n).map ((toSheaf k).map a)).app
          (op Y.unop.toSmoothSite) ((ordinaryCohomologyTransfers.{w, w', u} k F n).transfer f.unop
          (transferExtEquiv.{w, w', u} k X.unop.toSmoothSite F n e)) =
            (ordinaryCohomologyTransfers.{w, w', u} k G n).transfer f.unop _
        have h₁ := ordinaryCohomologyTransfers_apply.{w, w', u} k F n f.unop e
        have h₂ := ordinaryCoefficient_transferExtEquiv.{w, w', u} k n a Y.unop
          ((transferExtPresheaf.{w, u} k F n).map f e)
        have h₃ := congrArg (transferExtEquiv.{w, w', u} k Y.unop.toSmoothSite G n)
          (ConcreteCategory.congr_hom ((transferExtCoefficientMap.{w, u} k n a).naturality f) e)
        have h₄ := ordinaryCohomologyTransfers_apply.{w, w', u} k G n f.unop
          ((transferExtCoefficientMap.{w, u} k n a).app X e)
        have h₅ := ordinaryCoefficient_transferExtEquiv.{w, w', u} k n a X.unop e
        exact (congrArg
          (((SheafCohomology.presheafFunctor.{w', u + 1, u, u + 1}
            (SmoothSite.nisnevichTopology (Spec (.of k))) n).map
              ((toSheaf k).map a)).app (op Y.unop.toSmoothSite)) h₁).trans
          (h₂.trans (h₃.trans (h₄.symm.trans
            (congrArg ((ordinaryCohomologyTransfers.{w, w', u} k G n).transfer f.unop)
              h₅.symm)))) }

end Motivic.SheafWithTransfers
