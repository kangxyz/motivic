/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Field.Point.Unit

/-! # The actual inverse-image unit on every small-site point -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {S T : Scheme.{u}} (b : S ⟶ T)
  (Φ : (nisnevichTopology S).Point.{u + 1})
local instance : InitiallySmall.{u + 1} (baseChange b ⋙ Φ.fiber).Elements :=
  initiallySmall_of_essentiallySmall _
local notation "hcover" => CoverPreserving.of_isContinuous (baseChange b)
  (nisnevichTopology T) (nisnevichTopology S)

/-- On every actual field-valued representative the comap comparison is the
inverse-image adjunction unit followed by its original point-fiber injection. -/
@[reassoc]
theorem point_comapIso_unit_ι
    (G : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})
    (V : EtaleSeparatedFiniteType T) (x : (Φ.comap (baseChange b) hcover).fiber.obj V) :
    (Φ.comap (baseChange b) hcover).toPresheafFiber V x G.obj ≫
      (Φ.sheafFiberComapIso (baseChange b)
        hcover AddCommGrpCat.{u + 1}).hom.app G =
    ((imageAdjunction b).unit.app G).hom.app (op V) ≫
      Φ.toPresheafFiber ((baseChange b).obj V) x
        ((inverseImage b).obj G).obj := by
  let adj₁ := (imageAdjunction b).comp
    (Φ.skyscraperSheafAdjunction (A := AddCommGrpCat.{u + 1}))
  let adj₂ := (Φ.comap (baseChange b) hcover).skyscraperSheafAdjunction (A := AddCommGrpCat.{u + 1})
  let β := Φ.skyscraperSheafFunctorCompSheafPushforwardContinuous
    (baseChange b) hcover AddCommGrpCat.{u + 1}
  let α := (Φ.sheafFiberComapIso (baseChange b)
    hcover AddCommGrpCat.{u + 1}).hom.app G
  have h := unit_conjugateEquiv_symm adj₁ adj₂ β.hom G
  have hunit : adj₁.unit.app G = adj₂.unit.app G ≫
      (Φ.comap (baseChange b) hcover).skyscraperSheafFunctor.map α := by
    change adj₁.unit.app G ≫ 𝟙 _ = adj₂.unit.app G ≫
      (Φ.comap (baseChange b) hcover).skyscraperSheafFunctor.map α at h
    simpa only [Category.comp_id] using h
  have hx := congrArg (fun a => a.hom.app (op V) ≫ Pi.π _ x) hunit
  change (((imageAdjunction b).unit.app G).hom.app (op V) ≫
      (Φ.skyscraperSheafAdjunction.unit.app
        ((inverseImage b).obj G)).hom.app (op ((baseChange b).obj V))) ≫ Pi.π _ x =
    ((adj₂.unit.app G).hom.app (op V) ≫
      Limits.Pi.map (fun _ : (Φ.comap (baseChange b) hcover).fiber.obj V => α)) ≫ Pi.π _ x at hx
  rw [Category.assoc, Category.assoc, Limits.Pi.map_π, pointAdjunctionUnit_π] at hx
  have he := pointAdjunctionUnit_π (Φ.comap (baseChange b) hcover) G V x
  rw [← Category.assoc, he] at hx
  exact hx.symm


/-- Zero after the genuine inverse-image unit is zero in the original comapped
point fiber. The displayed marking is unchanged. -/
theorem comap_germ_eq_zero_of_inverseImage_unit_germ_eq_zero
    (G : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})
    (V : EtaleSeparatedFiniteType T)
    (x : (Φ.comap (baseChange b) hcover).fiber.obj V) (s : G.obj.obj (op V))
    (h : Φ.toPresheafFiber ((baseChange b).obj V) x ((inverseImage b).obj G).obj
      (((imageAdjunction b).unit.app G).hom.app (op V) s) = 0) :
    (Φ.comap (baseChange b) hcover).toPresheafFiber V x G.obj s = 0 := by
  let e := (Φ.sheafFiberComapIso (baseChange b) hcover AddCommGrpCat.{u + 1}).app G
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  rw [map_zero]
  exact (ConcreteCategory.congr_hom (point_comapIso_unit_ι b Φ G V x) s).trans h

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
