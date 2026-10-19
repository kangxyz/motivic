/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Injectives
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ImageExact
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Field.Point.Neighborhood
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Genuine point fibers of derived direct images

The fiber of a higher direct image is computed by applying the actual filtered
point-fiber functor to the direct image of a chosen injective resolution. The
comparison uses exactness of the point fiber, not exactness of direct image.
This is a resolution-level continuity step, not identification with cohomology
of a henselized scheme or with a filtered colimit of ordinary Ext groups.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {S T : Scheme.{u}} (b : T ⟶ S)
  (Φ : (nisnevichTopology S).Point.{u + 1})

local instance : (Φ.sheafFiber (A := AddCommGrpCat.{u + 1})).Additive :=
  Functor.additive_of_preserves_binary_products _


/-- The actual filtered neighborhood diagram uses geometric pullback by `b`. -/
def directImagePointDiagram
    (A : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) :
    Φ.fiber.Elementsᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.Elements.π Φ.fiber).op ⋙ (baseChange b).op ⋙ A.obj

/-- The genuine point fiber is exactly the colimit of the displayed pullback neighborhoods. -/
def directImagePointColimitIso
    (A : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) :
    colimit (directImagePointDiagram b Φ A) ≅
      Φ.sheafFiber.obj ((directImage b).obj A) := Iso.refl _

/-- Each coefficient map retains the original map on the geometrically pulled-back object. -/
@[reassoc]
theorem directImagePointInclusion_naturality
    {A B : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}} (a : A ⟶ B)
    (V : EtaleSeparatedFiniteType S) (v : Φ.fiber.obj V) :
    Φ.toPresheafFiber V v ((directImage b).obj A).obj ≫
        Φ.sheafFiber.map ((directImage b).map a) =
      a.hom.app (Opposite.op ((baseChange b).obj V)) ≫
        Φ.toPresheafFiber V v ((directImage b).obj B).obj :=
  Φ.toPresheafFiber_naturality ((directImage b).map a).hom V v

variable
  {F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}}
  (I : InjectiveResolution F)

/-- The three actual groups in the point-fiber direct-image resolution at degree `n`. -/
def directImageResolutionFiberStep (n : ℕ) : ShortComplex AddCommGrpCat.{u + 1} :=
  (((directImage b).mapHomologicalComplex _).obj I.cocomplex).sc n |>.map Φ.sheafFiber

/-- A higher-direct-image stalk is the homology of the actual filtered fiber groups. -/
def derivedDirectImagePointFiberIso (n : ℕ) :
    Φ.sheafFiber.obj (((directImage b).rightDerived n).obj F) ≅
      (directImageResolutionFiberStep b Φ I n).homology := by
  exact Φ.sheafFiber.mapIso (I.isoRightDerivedObj (directImage b) n) ≪≫
    (((((directImage b).mapHomologicalComplex _).obj I.cocomplex).sc n).mapHomologyIso
      Φ.sheafFiber).symm


/-- Naturality uses a genuine comparison of the chosen injective resolutions. -/
@[reassoc]
theorem derivedDirectImagePointFiberIso_naturality
    {G : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}} (f : F ⟶ G)
    (J : InjectiveResolution G) (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    Φ.sheafFiber.map (((directImage b).rightDerived n).map f) ≫
        (derivedDirectImagePointFiberIso b Φ J n).hom =
      (derivedDirectImagePointFiberIso b Φ I n).hom ≫
        ShortComplex.homologyMap (Φ.sheafFiber.mapShortComplex.map
          ((HomologicalComplex.shortComplexFunctor _ _ n).map
            (((directImage b).mapHomologicalComplex _).map φ))) := by
  dsimp only [derivedDirectImagePointFiberIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Functor.map_comp,
    I.isoRightDerivedObj_hom_naturality f J φ hφ (directImage b) n,
    Functor.map_comp, Category.assoc]
  rw [Category.assoc]
  apply congrArg (fun a => Φ.sheafFiber.map (I.isoRightDerivedObj (directImage b) n).hom ≫ a)
  exact ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map
      (((directImage b).mapHomologicalComplex _).map φ)) Φ.sheafFiber

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
