/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermInverseImage

/-! # Literal marked representatives under equality of field-valued base maps -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.SmoothSite
variable {B : Scheme.{u}} {X : SmoothSite B}
  (F : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (K : Type u) [Field K]

/-- The actual diagram injection at a literal field-valued marked neighborhood. -/
def smallFieldDiagramInjection (t : Spec (.of K) ⟶ X.left)
    (V : FiniteEtaleSite X.left) (a : Spec (.of K) ⟶ V.left)
    (ha : a ≫ V.hom = t) :
    F.obj (op ((FiniteEtaleSite.toSmoothSite X).obj V)) ⟶ smallFieldDiagramColimit F K t := by
  let : HasColimitsOfSize.{u, u + 1} AddCommGrpCat.{u + 1} :=
    hasColimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} AddCommGrpCat.{u + 1}
  exact colimit.ι ((Functor.Elements.π
    (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ X.left ⋙
      coyoneda.obj (op (Over.mk t)))).op ⋙ (FiniteEtaleSite.toSmoothSite X).op ⋙ F)
    (op (Functor.elementsMk
    (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ X.left ⋙
      coyoneda.obj (op (Over.mk t))) V (Over.homMk a ha)))

/-- Equality transport changes no underlying marked map and no section representative. -/
@[reassoc]
theorem smallFieldDiagramInjection_transport
    {t t' : Spec (.of K) ⟶ X.left} (h : t = t')
    (V : FiniteEtaleSite X.left) (a : Spec (.of K) ⟶ V.left)
    (ha : a ≫ V.hom = t) (ha' : a ≫ V.hom = t') :
    smallFieldDiagramInjection F K t V a ha ≫
      eqToHom (congrArg (smallFieldDiagramColimit F K) h) =
    smallFieldDiagramInjection F K t' V a ha' := by
  subst t'
  simp only [eqToHom_refl, Category.comp_id]

end Motivic.SmoothSite
