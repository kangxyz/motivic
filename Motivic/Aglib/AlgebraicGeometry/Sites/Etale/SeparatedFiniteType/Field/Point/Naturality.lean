/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Field.Point.Unit

/-! # Naturality of the actual inverse-image comparison in field-valued points -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {S T : Scheme.{u}} (b : S ⟶ T)
  (K L : Type u) [Field K] [Field L]
  (q : Spec (.of K) ⟶ S) (r : Spec (.of L) ⟶ S)
  [Etale q] [IsSeparated q] [QuasiCompact q]
  [Etale r] [IsSeparated r] [QuasiCompact r]

/-- An actual map of small-site field objects induces the native morphism of points. -/
def fieldPointHom (c : fieldObject K q ⟶ fieldObject L r) : fieldPoint K q ⟶ fieldPoint L r where
  hom := shrinkYoneda.flip.map c.op

/-- The same actual field-object map induces the comapped point morphism. -/
def relativeFieldPointHom (c : fieldObject K q ⟶ fieldObject L r) :
    relativeFieldPoint b K q ⟶ relativeFieldPoint b L r where
  hom := Functor.whiskerLeft (baseChange b) (fieldPointHom K L q r c).hom

/-- On a literal representative the induced point map is composition of the actual field maps. -/
@[reassoc]
theorem relativeFieldPointHom_ι (c : fieldObject K q ⟶ fieldObject L r)
    (G : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})
    (V : EtaleSeparatedFiniteType T) (a : fieldObject L r ⟶ (baseChange b).obj V) :
    (relativeFieldPoint b L r).toPresheafFiber V
        (shrinkYonedaObjObjEquiv.{u + 1}.symm a) G.obj ≫
      (relativeFieldPointHom b K L q r c).sheafFiber.app G =
    (relativeFieldPoint b K q).toPresheafFiber V
      (shrinkYonedaObjObjEquiv.{u + 1}.symm (c ≫ a)) G.obj := by
  dsimp only [GrothendieckTopology.Point.Hom.sheafFiber,
    GrothendieckTopology.Point.Hom.presheafFiber, Functor.whiskerLeft_app]
  simp only [GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc]
  apply congrArg (fun x => (relativeFieldPoint b K q).toPresheafFiber V x G.obj)
  exact shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{u + 1} c.op a

/-- Naturality uses the original inverse-image sheaf restriction, not transported maps. -/
@[reassoc]
theorem relativeFieldPointInverseImageIso_field_naturality
    (c : fieldObject K q ⟶ fieldObject L r)
    (G : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) :
    (relativeFieldPointHom b K L q r c).sheafFiber.app G ≫
      (relativeFieldPointInverseImageIso b K q).hom.app G =
    (relativeFieldPointInverseImageIso b L r).hom.app G ≫
      ((inverseImage b).obj G).obj.map c.op := by
  apply (relativeFieldPoint b L r).presheafFiber_hom_ext
  intro V x
  obtain ⟨a, rfl⟩ := shrinkYonedaObjObjEquiv.{u + 1}.symm.surjective x
  erw [← Category.assoc, relativeFieldPointHom_ι,
    relativeFieldPointInverseImageIso_ι, relativeFieldPointInverseImageIso_ι_assoc]
  simp only [op_comp, Functor.map_comp]

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
