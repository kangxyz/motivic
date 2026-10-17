module

import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoproductUnitEndomorphism

/-! # Literal unit endomorphisms detected through native coproduct pullbacks -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom

universe u

example (X Y : Scheme.{u})
    (a b : SheafOfModules.unit (X ⨿ Y).ringCatSheaf ⟶
      SheafOfModules.unit (X ⨿ Y).ringCatSheaf)
    (hl : unitEndomorphismPullback (coprod.inl : X ⟶ X ⨿ Y) a =
      unitEndomorphismPullback (coprod.inl : X ⟶ X ⨿ Y) b)
    (hr : unitEndomorphismPullback (coprod.inr : Y ⟶ X ⨿ Y) a =
      unitEndomorphismPullback (coprod.inr : Y ⟶ X ⨿ Y) b) : a = b :=
  unitEndomorphism_ext_coprod X Y a b hl hr

example {X Y Z : Scheme.{u}} (a : X ⟶ Z) (b : Y ⟶ Z) (M : Z.Modules)
    (δ : SheafOfModules.unit Z.ringCatSheaf ⟶ M)
    (E : (Scheme.Modules.pullback (coprod.desc a b)).obj M ≅
      SheafOfModules.unit (X ⨿ Y).ringCatSheaf)
    (e : (Scheme.Modules.pullback a).obj M ≅ SheafOfModules.unit X.ringCatSheaf)
    (h : (Scheme.Modules.restrictFunctor (coprod.inl : X ⟶ X ⨿ Y)).map E.hom ≫
      (restrictUnitIso _).hom = (coprodPullbackRestrictLeft a b).hom.app M ≫ e.hom) :
    unitEndomorphismPullback (coprod.inl : X ⟶ X ⨿ Y)
      (pullbackSectionMap (coprod.desc a b) δ ≫ E.hom) = pullbackSectionMap a δ ≫ e.hom :=
  unitEndomorphismPullback_coprod_inl_coordinate a b M δ E e h
