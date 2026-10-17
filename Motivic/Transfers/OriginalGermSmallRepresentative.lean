/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermInverseImage
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleFieldPointNaturality

/-! # Actual representatives in the original-to-small germ comparison -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.SmoothSite.RelativeNisnevichNeighborhood
variable {S : Scheme.{u}} [IsAffine S] {U X : SmoothSite S}
  (f : U ⟶ X) [Etale f.left] (u : U.left)
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- The small-site comparison retains the original representative and its literal
identity reassociation of structural maps. -/
@[reassoc]
theorem smallOriginalFiberIso_ι (M : NisnevichNeighborhood U u) :
    colimit.ι ((smallForget f u).op ⋙ F)
        (op ((toSmall f u).obj (compose f u M))) ≫
      (smallOriginalFiberIso f u F).hom =
    F.map ((composeForgetIso f u).app M).inv.op ≫
      (nisnevichPointFiberCocone U u F).ι.app (op M) := by
  dsimp only [smallOriginalFiberIso, Iso.trans_hom, Iso.symm_hom]
  erw [Functor.Final.ι_colimitIso_inv_assoc (toSmall f u).op
    ((smallForget f u).op ⋙ F) (op (compose f u M))]
  rw [HasColimit.ι_isoOfNatIso_hom_assoc]
  change F.map (𝟙 _) ≫ _ = _
  rw [F.map_id, Category.id_comp]
  exact originalFiberIso_ι f u F M

/-- Conversely, the original cocone map lands in the actual small marked neighborhood. -/
@[reassoc]
theorem original_ι_smallOriginalFiberIso_inv (M : NisnevichNeighborhood U u) :
    (nisnevichPointFiberCocone U u F).ι.app (op M) ≫
      (smallOriginalFiberIso f u F).inv =
    F.map ((composeForgetIso f u).app M).hom.op ≫
      colimit.ι ((smallForget f u).op ⋙ F)
        (op ((toSmall f u).obj (compose f u M))) := by
  apply (cancel_mono (smallOriginalFiberIso f u F).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    smallOriginalFiberIso_ι]
  rw [← Category.assoc, ← F.map_comp, ← op_comp, Iso.inv_hom_id,
    op_id, F.map_id, Category.id_comp]

end Motivic.SmoothSite.RelativeNisnevichNeighborhood
