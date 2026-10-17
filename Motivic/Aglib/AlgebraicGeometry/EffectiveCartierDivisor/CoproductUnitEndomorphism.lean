/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateUnitOnOpen
public import Aglib.AlgebraicGeometry.Modules.Restriction.Unit
public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.CoproductRestriction
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.SectionDualFunctional

/-! # Detecting exact unit endomorphisms on coproduct components

The original pullback and open restriction are compared by their native unit
isomorphisms. Equality is detected on the two actual coproduct components.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Normalized pullback of a unit endomorphism agrees with its actual open restriction. -/
theorem unitEndomorphismPullback_eq_iff_restrict {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f]
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    unitEndomorphismPullback f a = b ↔
      (Scheme.Modules.restrictFunctor f).map a ≫ (restrictUnitIso f).hom =
        (restrictUnitIso f).hom ≫ b := by
  have hu : (restrictFunctorIsoPullback f).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
      (pullbackUnitIso f).hom = (restrictUnitIso f).hom :=
    restrictFunctorIsoPullback_hom_unit f
  have hn := (restrictFunctorIsoPullback f).hom.naturality a
  constructor
  · intro h
    rw [← h, ← hu, unitEndomorphismPullback]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg (fun t => t ≫ (pullbackUnitIso f).hom) hn
  · intro h
    apply (cancel_epi (restrictUnitIso f).hom).mp
    rw [← h, ← hu, unitEndomorphismPullback]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact (congrArg (fun t => t ≫ (pullbackUnitIso f).hom) hn).symm

/-- The native component restriction equation gives the literal normalized pullback. -/
theorem unitEndomorphismPullback_eq_of_restrict {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f]
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (h : (Scheme.Modules.restrictFunctor f).map a ≫ (restrictUnitIso f).hom =
      (restrictUnitIso f).hom ≫ b) : unitEndomorphismPullback f a = b :=
  (unitEndomorphismPullback_eq_iff_restrict f a b).mpr h

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules

/-- Actual module-sheaf morphisms on a coproduct are determined by the two restrictions. -/
theorem hom_ext_coprod_restrict (X Y : Scheme.{u})
    {M N : (X ⨿ Y).Modules} (a b : M ⟶ N)
    (hl : (restrictFunctor (coprod.inl : X ⟶ X ⨿ Y)).map a =
      (restrictFunctor (coprod.inl : X ⟶ X ⨿ Y)).map b)
    (hr : (restrictFunctor (coprod.inr : Y ⟶ X ⨿ Y)).map a =
      (restrictFunctor (coprod.inr : Y ⟶ X ⨿ Y)).map b) : a = b := by
  let C : Bool → Scheme.{u} := fun i => cond i X Y
  let j : ∀ i, C i ⟶ X ⨿ Y := fun i => by
    cases i
    · exact coprod.inr
    · exact coprod.inl
  have hopen : ∀ i, IsOpenImmersion (j i) := by
    intro i; cases i <;> dsimp [j] <;> infer_instance
  let (i : Bool) : IsOpenImmersion (j i) := hopen i
  have hcover : ∀ x : (X ⨿ Y : Scheme.{u}), ∃ (i : Bool) (y : C i), j i y = x := by
    intro x
    obtain ⟨x | x, rfl⟩ := (AlgebraicGeometry.coprodMk X Y).surjective x
    · exact ⟨true, x, (AlgebraicGeometry.coprodMk_inl X Y x).symm⟩
    · exact ⟨false, x, (AlgebraicGeometry.coprodMk_inr X Y x).symm⟩
  let H := InternalHom.sheaf (X ⨿ Y) M N
  let A : TopCat.Sheaf Ab (X ⨿ Y : Scheme.{u}) := ⟨H.val.presheaf, H.isSheaf⟩
  apply (InternalHom.globalHomEquiv (X ⨿ Y) M N).injective
  apply A.eq_of_locally_eq' (fun i => (j i).opensRange) ⊤
    (fun _ => homOfLE le_top) (InternalHom.restrictionRanges_cover C j hcover).ge
  intro i
  change H.val.map (homOfLE le_top).op (InternalHom.globalHomEquiv (X ⨿ Y) M N a) =
    H.val.map (homOfLE le_top).op (InternalHom.globalHomEquiv (X ⨿ Y) M N b)
  rw [InternalHom.globalHomEquiv_restrict, InternalHom.globalHomEquiv_restrict]
  apply congrArg
  cases i
  · exact hr
  · exact hl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

open Scheme.Modules.Invertible

private theorem pullbackRestrict_comparison_unit {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) :
    (Functor.isoWhiskerLeft (Scheme.Modules.pullback g) (restrictFunctorIsoPullback f) ≪≫
      Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr h).hom.app
        (SheafOfModules.unit Z.ringCatSheaf) ≫ (pullbackUnitIso k).hom =
      (Scheme.Modules.restrictFunctor f).map (pullbackUnitIso g).hom ≫
        (restrictUnitIso f).hom := by
  change (restrictFunctorIsoPullback f).hom.app
      ((Scheme.Modules.pullback g).obj (SheafOfModules.unit Z.ringCatSheaf)) ≫
    (Scheme.Modules.pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
    (Scheme.Modules.pullbackCongr h).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
    (pullbackUnitIso k).hom = _
  rw [pullbackUnitIso_congr, pullbackUnitIso_comp]
  rw [← Category.assoc, ← (restrictFunctorIsoPullback f).hom.naturality]
  rw [Category.assoc]
  exact congrArg (fun t => (Scheme.Modules.restrictFunctor f).map
    (pullbackUnitIso g).hom ≫ t)
      (show (restrictFunctorIsoPullback f).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
          (pullbackUnitIso f).hom = (restrictUnitIso f).hom from
        restrictFunctorIsoPullback_hom_unit f)

private theorem pullbackSectionMap_restrict_comparison {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    {M : Z.Modules} (δ : SheafOfModules.unit Z.ringCatSheaf ⟶ M) :
    (Scheme.Modules.restrictFunctor f).map (pullbackSectionMap g δ) ≫
      (Functor.isoWhiskerLeft (Scheme.Modules.pullback g) (restrictFunctorIsoPullback f) ≪≫
        Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr h).hom.app M =
      (restrictUnitIso f).hom ≫ pullbackSectionMap k δ := by
  let e := Functor.isoWhiskerLeft (Scheme.Modules.pullback g) (restrictFunctorIsoPullback f) ≪≫
    Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr h
  have hu : (Scheme.Modules.restrictFunctor f).map (pullbackUnitIso g).inv ≫
      e.hom.app (SheafOfModules.unit Z.ringCatSheaf) =
        (restrictUnitIso f).hom ≫ (pullbackUnitIso k).inv := by
    apply (cancel_mono (pullbackUnitIso k).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [pullbackRestrict_comparison_unit]
    rw [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  change (Scheme.Modules.restrictFunctor f).map (pullbackSectionMap g δ) ≫ e.hom.app M = _
  simp only [pullbackSectionMap, Functor.map_comp, Category.assoc]
  have hn := e.hom.naturality δ
  change (Scheme.Modules.restrictFunctor f).map ((Scheme.Modules.pullback g).map δ) ≫
    e.hom.app M = e.hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
      (Scheme.Modules.pullback k).map δ at hn
  rw [hn]
  exact congrArg (fun t => t ≫ (Scheme.Modules.pullback k).map δ) hu

/-- The literal left frame restriction computes the normalized coordinate of a pulled section. -/
theorem unitEndomorphismPullback_coprod_inl_coordinate {X Y Z : Scheme.{u}}
    (a : X ⟶ Z) (b : Y ⟶ Z) (M : Z.Modules)
    (δ : SheafOfModules.unit Z.ringCatSheaf ⟶ M)
    (E : (Scheme.Modules.pullback (coprod.desc a b)).obj M ≅
      SheafOfModules.unit (X ⨿ Y).ringCatSheaf)
    (e : (Scheme.Modules.pullback a).obj M ≅ SheafOfModules.unit X.ringCatSheaf)
    (h : (Scheme.Modules.restrictFunctor (coprod.inl : X ⟶ X ⨿ Y)).map E.hom ≫
      (restrictUnitIso _).hom = (coprodPullbackRestrictLeft a b).hom.app M ≫ e.hom) :
    unitEndomorphismPullback (coprod.inl : X ⟶ X ⨿ Y)
      (pullbackSectionMap (coprod.desc a b) δ ≫ E.hom) = pullbackSectionMap a δ ≫ e.hom := by
  apply unitEndomorphismPullback_eq_of_restrict
  rw [Functor.map_comp, Category.assoc, h, ← Category.assoc]
  rw [show (Scheme.Modules.restrictFunctor (coprod.inl : X ⟶ X ⨿ Y)).map
      (pullbackSectionMap (coprod.desc a b) δ) ≫ (coprodPullbackRestrictLeft a b).hom.app M =
        (restrictUnitIso _).hom ≫ pullbackSectionMap a δ from
    pullbackSectionMap_restrict_comparison _ _ _ (coprod.inl_desc a b) δ]
  rw [Category.assoc]

/-- The literal right frame restriction computes the normalized coordinate of a pulled section. -/
theorem unitEndomorphismPullback_coprod_inr_coordinate {X Y Z : Scheme.{u}}
    (a : X ⟶ Z) (b : Y ⟶ Z) (M : Z.Modules)
    (δ : SheafOfModules.unit Z.ringCatSheaf ⟶ M)
    (E : (Scheme.Modules.pullback (coprod.desc a b)).obj M ≅
      SheafOfModules.unit (X ⨿ Y).ringCatSheaf)
    (e : (Scheme.Modules.pullback b).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (h : (Scheme.Modules.restrictFunctor (coprod.inr : Y ⟶ X ⨿ Y)).map E.hom ≫
      (restrictUnitIso _).hom = (coprodPullbackRestrictRight a b).hom.app M ≫ e.hom) :
    unitEndomorphismPullback (coprod.inr : Y ⟶ X ⨿ Y)
      (pullbackSectionMap (coprod.desc a b) δ ≫ E.hom) = pullbackSectionMap b δ ≫ e.hom := by
  apply unitEndomorphismPullback_eq_of_restrict
  rw [Functor.map_comp, Category.assoc, h, ← Category.assoc]
  rw [show (Scheme.Modules.restrictFunctor (coprod.inr : Y ⟶ X ⨿ Y)).map
      (pullbackSectionMap (coprod.desc a b) δ) ≫ (coprodPullbackRestrictRight a b).hom.app M =
        (restrictUnitIso _).hom ≫ pullbackSectionMap b δ from
    pullbackSectionMap_restrict_comparison _ _ _ (coprod.inr_desc a b) δ]
  rw [Category.assoc]

/-- Two normalized component pullbacks determine the original unit endomorphism. -/
theorem unitEndomorphism_ext_coprod (X Y : Scheme.{u})
    (a b : SheafOfModules.unit (X ⨿ Y).ringCatSheaf ⟶
      SheafOfModules.unit (X ⨿ Y).ringCatSheaf)
    (hl : unitEndomorphismPullback (coprod.inl : X ⟶ X ⨿ Y) a =
      unitEndomorphismPullback (coprod.inl : X ⟶ X ⨿ Y) b)
    (hr : unitEndomorphismPullback (coprod.inr : Y ⟶ X ⨿ Y) a =
      unitEndomorphismPullback (coprod.inr : Y ⟶ X ⨿ Y) b) : a = b := by
  apply hom_ext_coprod_restrict X Y a b
  · apply (cancel_mono (restrictUnitIso (coprod.inl : X ⟶ X ⨿ Y)).hom).mp
    exact ((unitEndomorphismPullback_eq_iff_restrict _ _ _).mp hl).trans
      ((unitEndomorphismPullback_eq_iff_restrict _ _ _).mp rfl).symm
  · apply (cancel_mono (restrictUnitIso (coprod.inr : Y ⟶ X ⨿ Y)).hom).mp
    exact ((unitEndomorphismPullback_eq_iff_restrict _ _ _).mp hr).trans
      ((unitEndomorphismPullback_eq_iff_restrict _ _ _).mp rfl).symm

end AlgebraicGeometry.Scheme.Hom
