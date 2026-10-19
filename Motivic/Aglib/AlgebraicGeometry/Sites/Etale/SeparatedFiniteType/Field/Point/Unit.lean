/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Field.Point.Neighborhood

/-! # Canonical representative maps for the genuine inverse-image comparison -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

/-- A coordinate of the actual point adjunction unit is its original colimit injection. -/
@[reassoc]
theorem pointAdjunctionUnit_π {S : Scheme.{u}}
    (Φ : (nisnevichTopology S).Point.{u + 1})
    (G : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
    (V : EtaleSeparatedFiniteType S) (x : Φ.fiber.obj V) :
    (Φ.skyscraperSheafAdjunction.unit.app G).hom.app (op V) ≫ Pi.π _ x =
      Φ.toPresheafFiber V x G.obj := by
  change Pi.lift (fun y => Φ.toPresheafFiber V y G.obj ≫ 𝟙 _) ≫ Pi.π _ x = _
  exact (Pi.lift_comp_π (fun y => Φ.toPresheafFiber V y G.obj ≫ 𝟙 _) x).trans
    (Category.comp_id _)

variable {S T : Scheme.{u}} (b : S ⟶ T) (K : Type u) [Field K]
  (q : Spec (.of K) ⟶ S) [Etale q] [IsSeparated q] [QuasiCompact q]

/-- On every actual field-valued representative the comap comparison is the
inverse-image adjunction unit followed by its original point-fiber injection. -/
@[reassoc]
theorem relativeFieldPoint_comapIso_ι
    (G : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})
    (V : EtaleSeparatedFiniteType T) (x : (relativeFieldPoint b K q).fiber.obj V) :
    (relativeFieldPoint b K q).toPresheafFiber V x G.obj ≫
      ((fieldPoint K q).sheafFiberComapIso (baseChange b)
        (CoverPreserving.of_isContinuous (baseChange b) _ _) AddCommGrpCat.{u + 1}).hom.app G =
    ((imageAdjunction b).unit.app G).hom.app (op V) ≫
      (fieldPoint K q).toPresheafFiber ((baseChange b).obj V) x
        ((inverseImage b).obj G).obj := by
  let adj₁ := (imageAdjunction b).comp
    ((fieldPoint K q).skyscraperSheafAdjunction (A := AddCommGrpCat.{u + 1}))
  let adj₂ := (relativeFieldPoint b K q).skyscraperSheafAdjunction (A := AddCommGrpCat.{u + 1})
  let β := (fieldPoint K q).skyscraperSheafFunctorCompSheafPushforwardContinuous
    (baseChange b) (CoverPreserving.of_isContinuous (baseChange b)
      (nisnevichTopology T) (nisnevichTopology S)) AddCommGrpCat.{u + 1}
  let α := ((fieldPoint K q).sheafFiberComapIso (baseChange b)
    (CoverPreserving.of_isContinuous (baseChange b) _ _) AddCommGrpCat.{u + 1}).hom.app G
  have h := unit_conjugateEquiv_symm adj₁ adj₂ β.hom G
  have hunit : adj₁.unit.app G = adj₂.unit.app G ≫
      (relativeFieldPoint b K q).skyscraperSheafFunctor.map α := by
    change adj₁.unit.app G ≫ 𝟙 _ = adj₂.unit.app G ≫
      (relativeFieldPoint b K q).skyscraperSheafFunctor.map α at h
    simpa only [Category.comp_id] using h
  have hx := congrArg (fun a => a.hom.app (op V) ≫ Pi.π _ x) hunit
  change (((imageAdjunction b).unit.app G).hom.app (op V) ≫
      ((fieldPoint K q).skyscraperSheafAdjunction.unit.app
        ((inverseImage b).obj G)).hom.app (op ((baseChange b).obj V))) ≫ Pi.π _ x =
    ((adj₂.unit.app G).hom.app (op V) ≫
      Limits.Pi.map (fun _ : (relativeFieldPoint b K q).fiber.obj V => α)) ≫ Pi.π _ x at hx
  rw [Category.assoc, Category.assoc, Limits.Pi.map_π, pointAdjunctionUnit_π] at hx
  have he := pointAdjunctionUnit_π (relativeFieldPoint b K q) G V x
  rw [← Category.assoc, he] at hx
  exact hx.symm


/-- A represented field-point injection becomes the literal restriction along
its marked field-valued point, rather than an unspecified isomorphic map. -/
@[reassoc]
theorem fieldPointPresheafFiberIso_ι
    (G : (EtaleSeparatedFiniteType S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (V : EtaleSeparatedFiniteType S) (a : fieldObject K q ⟶ V) :
    (fieldPoint K q).toPresheafFiber V (shrinkYonedaObjObjEquiv.{u + 1}.symm a) G ≫
      (fieldPointPresheafFiberIso K q AddCommGrpCat.{u + 1}).hom.app G = G.map a.op := by
  let e := fieldPointPresheafFiberIso K q AddCommGrpCat.{u + 1}
  let z := shrinkYonedaObjObjEquiv.{u + 1}.symm (𝟙 (fieldObject K q))
  have hz : (fieldPoint K q).fiber.map a z = shrinkYonedaObjObjEquiv.{u + 1}.symm a := by
    change (shrinkYoneda.{u + 1}.map a).app (op (fieldObject K q))
      (shrinkYonedaObjObjEquiv.{u + 1}.symm (𝟙 (fieldObject K q))) = _
    rw [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm, Category.id_comp]
    rfl
  have hw := (fieldPoint K q).toPresheafFiber_w a z G
  rw [hz] at hw
  have he : (fieldPoint K q).toPresheafFiber (fieldObject K q) z G ≫ e.hom.app G = 𝟙 _ :=
    congrArg (fun a => a.app G) e.inv_hom_id
  exact (congrArg (fun t => t ≫ e.hom.app G) hw.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t => G.map a.op ≫ t) he).trans (Category.comp_id _)))


/-- The existing inverse-image comparison acts on representatives by its actual
adjunction unit and the actual small-site field-point restriction. -/
@[reassoc]
theorem relativeFieldPointInverseImageIso_ι
    (G : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})
    (V : EtaleSeparatedFiniteType T) (a : fieldObject K q ⟶ (baseChange b).obj V) :
    (relativeFieldPoint b K q).toPresheafFiber V
        (shrinkYonedaObjObjEquiv.{u + 1}.symm a) G.obj ≫
      (relativeFieldPointInverseImageIso b K q).hom.app G =
    ((imageAdjunction b).unit.app G).hom.app (op V) ≫
      ((inverseImage b).obj G).obj.map a.op := by
  change (relativeFieldPoint b K q).toPresheafFiber V
      (shrinkYonedaObjObjEquiv.{u + 1}.symm a) G.obj ≫
    (((fieldPoint K q).sheafFiberComapIso (baseChange b)
      (CoverPreserving.of_isContinuous (baseChange b) _ _) AddCommGrpCat.{u + 1}).hom.app G ≫
      (fieldPointPresheafFiberIso K q AddCommGrpCat.{u + 1}).hom.app
        ((inverseImage b).obj G).obj) = _
  rw [relativeFieldPoint_comapIso_ι_assoc, fieldPointPresheafFiberIso_ι]


/-- On every actual marked field point, the literal neighborhood-colimit map is
the genuine inverse-image unit followed by restriction along that marked point. -/
@[reassoc]
theorem fieldNeighborhoodInverseImageIso_ι
    (G : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})
    (V : EtaleSeparatedFiniteType T) (a : fieldObject K q ⟶ (baseChange b).obj V) :
    colimit.ι ((Functor.Elements.π
      (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ T ⋙
        coyoneda.obj (op (Over.mk (q ≫ b))))).op ⋙ G.obj)
      (op ((pointElementsToNeighborhood b K q).obj
        ((relativeFieldPoint b K q).fiber.elementsMk V
          (shrinkYonedaObjObjEquiv.{u + 1}.symm a)))) ≫
        (fieldNeighborhoodInverseImageIso b K q G).hom =
    ((imageAdjunction b).unit.app G).hom.app (op V) ≫
      ((inverseImage b).obj G).obj.map a.op := by
  dsimp only [fieldNeighborhoodInverseImageIso, fieldNeighborhoodFiberIso,
    Iso.trans_hom, Iso.symm_hom]
  erw [Functor.Final.ι_colimitIso_inv_assoc (pointElementsToNeighborhood b K q).op
    ((Functor.Elements.π _).op ⋙ G.obj)
    (op ((relativeFieldPoint b K q).fiber.elementsMk V
      (shrinkYonedaObjObjEquiv.{u + 1}.symm a)))]
  exact relativeFieldPointInverseImageIso_ι b K q G V a

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
