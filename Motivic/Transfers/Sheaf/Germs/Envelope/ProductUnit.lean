/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Envelope.Product
public import Motivic.Transfers.Sheaf.Germs.Envelope.Unit

/-! # The existing envelope embedding is the actual product of image units -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable (k : Type u) [Field k] (P : SheafWithTransfers.{u + 1} k)
  (X : SmoothSite (Spec (.of k)))

/-- The component of the original embedding is the genuine image-adjunction unit. -/
theorem toOriginalGermEnvelope_factor_unit (x : X.left) :
    (EtaleSeparatedFiniteType.restrict X AddCommGrpCat).map
        ((toSheaf k).map (toOriginalGermEnvelope k P)) ≫ originalEnvelopeToFactor k P X x =
      (Scheme.EtaleSeparatedFiniteType.imageAdjunction (X.left.fromSpecResidueField x)).unit.app
        ((EtaleSeparatedFiniteType.restrict X AddCommGrpCat).obj ((toSheaf k).obj P)) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  ext a
  apply (Scheme.EtaleSeparatedFiniteType.originalFiberSectionsEquiv V.unop x
    (originalResidueCoefficient X (envelopeCoefficient k P) x)).injective
  funext v
  change Scheme.EtaleSeparatedFiniteType.originalFiberSectionsEquiv V.unop x
    (originalResidueCoefficient X (envelopeCoefficient k P) x)
      (originalEnvelopeCoordinate k P X V.unop x
        (((EtaleSeparatedFiniteType.restrict X AddCommGrpCat).map
          ((toSheaf k).map (toOriginalGermEnvelope k P))).hom.app V a)) v = _
  rw [originalEnvelopeCoordinate_apply]
  exact ConcreteCategory.congr_hom
    (originalFiberGermIso_section X (envelopeCoefficient k P) V.unop x v) a

/-- Under the genuine sheaf isomorphism, the original embedding is the product of units. -/
theorem toOriginalGermEnvelope_product_unit :
    (EtaleSeparatedFiniteType.restrict X AddCommGrpCat).map
        ((toSheaf k).map (toOriginalGermEnvelope k P)) ≫
      (originalEnvelopeProductIso k P X).hom =
    Limits.Pi.lift (fun x : X.left ↦
      (Scheme.EtaleSeparatedFiniteType.imageAdjunction (X.left.fromSpecResidueField x)).unit.app
        ((EtaleSeparatedFiniteType.restrict X AddCommGrpCat).obj ((toSheaf k).obj P))) := by
  apply Limits.Pi.hom_ext
  intro x
  change (_ ≫ originalEnvelopeToProduct k P X) ≫ _ = _
  rw [Category.assoc, originalEnvelopeToProduct_π]
  erw [Limits.Pi.lift_comp_π]
  exact toOriginalGermEnvelope_factor_unit k P X x

end Motivic.SheafWithTransfers
