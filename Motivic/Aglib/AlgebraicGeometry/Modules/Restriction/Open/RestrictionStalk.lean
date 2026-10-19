/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Pushforward.Affine.Stalk

/-!
# Structure-stalk-linear open restriction

The actual open-restriction stalk comparison is linear for the canonical
structure-stalk actions. The ring map is the inverse of the actual open
immersion stalk map, not a transported replacement action.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Stalk

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X)

/-- The canonical target action in the composed ordinary stalk-functor spelling. -/
local instance openRestrictionTargetModule (M : Y.Modules) :
    Module (Y.presheaf.stalk (f x))
      ((Scheme.Modules.toPresheaf Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).obj M) :=
  stalkModule (f x) M

/-- The actual open-immersion stalk map on a section over the image neighborhood. -/
@[reassoc] theorem appIso_germ (U : X.Opens) (hx : x ∈ U) :
    (f.appIso U).hom ≫ X.presheaf.germ U x hx =
      Y.presheaf.germ (f ''ᵁ U) (f x) ⟨x, hx, rfl⟩ ≫ f.stalkMap x := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE, Category.assoc,
    TopCat.Presheaf.germ_res]
  exact (f.germ_stalkMap _ _ _).symm

/-- The inverse structure-stalk map uses the literal inverse section map. -/
@[reassoc] theorem germ_inv_stalkMap (U : X.Opens) (hx : x ∈ U) :
    X.presheaf.germ U x hx ≫ inv (f.stalkMap x) =
      (f.appIso U).inv ≫ Y.presheaf.germ (f ''ᵁ U) (f x) ⟨x, hx, rfl⟩ := by
  apply (cancel_mono (f.stalkMap x)).mp
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.assoc,
    ← appIso_germ, Iso.inv_hom_id_assoc]

/-- The existing open restriction stalk map sends a germ to the same image-neighborhood germ. -/
theorem openRestriction_germ (M : Y.Modules) (U : X.Opens) (hx : x ∈ U)
    (m : M.val.obj (op (f ''ᵁ U))) :
    (Scheme.Modules.restrictStalkNatIso f x).hom.app M
        (((Scheme.Modules.restrictFunctor f).obj M).presheaf.germ U x hx m) =
      M.presheaf.germ (f ''ᵁ U) (f x) ⟨x, hx, rfl⟩ m :=
  ConcreteCategory.congr_hom (Scheme.Modules.germ_restrictStalkNatIso_hom_app f x M hx) m

/-- The actual open-restriction stalk comparison respects the canonical scalar action. -/
theorem openRestriction_smul (M : Y.Modules)
    (r : X.presheaf.stalk x)
    (m : ((Scheme.Modules.restrictFunctor f).obj M).presheaf.stalk x) :
    (Scheme.Modules.restrictStalkNatIso f x).hom.app M (r • m) =
      inv (f.stalkMap x) r •
        ((Scheme.Modules.restrictStalkNatIso f x).hom.app M m : M.presheaf.stalk (f x)) := by
  obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hxV, m, rfl⟩ :=
    ((Scheme.Modules.restrictFunctor f).obj M).presheaf.exists_le_germ_eq m hxU
  rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV r]
  erw [← PresheafOfModules.germ_smul (R := X.presheaf)
    ((Scheme.Modules.restrictFunctor f).obj M).val x V hxV]
  erw [openRestriction_germ, openRestriction_germ]
  have hr := ConcreteCategory.congr_hom (germ_inv_stalkMap f x V hxV)
    (X.presheaf.map (homOfLE hVU).op r)
  change inv (f.stalkMap x) (X.presheaf.germ V x hxV _) = _ at hr
  rw [hr]
  exact PresheafOfModules.germ_smul (R := Y.presheaf) M.val (f x) (f ''ᵁ V)
    ⟨x, hxV, rfl⟩ ((f.appIso V).inv (X.presheaf.map (homOfLE hVU).op r)) m

/-- The existing additive stalk isomorphism, linear for the inverse actual
structure-stalk map of the open immersion. -/
def openRestrictionLinearEquiv (M : Y.Modules) :
    ((functor x).obj ((Scheme.Modules.restrictFunctor f).obj M)) ≃ₗ[X.presheaf.stalk x]
      ((ModuleCat.restrictScalars (inv (f.stalkMap x)).hom).obj ((functor (f x)).obj M)) :=
  { __ := ((Scheme.Modules.restrictStalkNatIso f x).app M).addCommGroupIsoToAddEquiv
    map_smul' := openRestriction_smul f x M }

/-- Open restriction commutes naturally with the actual structure-stalk module,
after restriction along the inverse of the actual structure-stalk map. -/
def openRestrictionIso :
    Scheme.Modules.restrictFunctor f ⋙ functor x ≅
      functor (f x) ⋙ ModuleCat.restrictScalars (inv (f.stalkMap x)).hom :=
  NatIso.ofComponents (fun M => (openRestrictionLinearEquiv f x M).toModuleIso) (fun φ => by
    ext m
    exact ConcreteCategory.congr_hom ((Scheme.Modules.restrictStalkNatIso f x).hom.naturality φ) m)

/-- The linear comparison retains the literal original additive stalk map. -/
theorem openRestrictionIso_hom_apply (M : Y.Modules)
    (m : ((Scheme.Modules.restrictFunctor f).obj M).presheaf.stalk x) :
    (openRestrictionIso f x).hom.app M m =
      (Scheme.Modules.restrictStalkNatIso f x).hom.app M m := rfl

/-- Every original module-sheaf morphism satisfies the actual linear stalk square. -/
@[reassoc] theorem openRestrictionIso_naturality {M N : Y.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.restrictFunctor f ⋙ functor x).map φ ≫
        (openRestrictionIso f x).hom.app N =
      (openRestrictionIso f x).hom.app M ≫
        (functor (f x) ⋙ ModuleCat.restrictScalars (inv (f.stalkMap x)).hom).map φ :=
  (openRestrictionIso f x).hom.naturality φ

/-- The actual open-restriction comparison preserves arbitrary complexes and
all their original differentials. -/
def openRestrictionComplexIso {ι : Type*} (c : ComplexShape ι) :
    (Scheme.Modules.restrictFunctor f ⋙ functor x).mapHomologicalComplex c ≅
      (functor (f x) ⋙ ModuleCat.restrictScalars
        (inv (f.stalkMap x)).hom).mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex (openRestrictionIso f x) c

/-- Every degree of the complex comparison is the same actual linear stalk map. -/
theorem openRestrictionComplexIso_hom_f {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex Y.Modules c) (n : ι) :
    ((openRestrictionComplexIso f x c).app K).hom.f n =
      (openRestrictionIso f x).hom.app (K.X n) := rfl

/-- The literal differential square of the original restricted sheaf complex. -/
theorem openRestrictionComplexIso_hom_comm {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex Y.Modules c) (n m : ι) :
    (((Scheme.Modules.restrictFunctor f ⋙ functor x).mapHomologicalComplex c).obj K).d n m ≫
        ((openRestrictionComplexIso f x c).app K).hom.f m =
      ((openRestrictionComplexIso f x c).app K).hom.f n ≫
        (((functor (f x) ⋙ ModuleCat.restrictScalars
          (inv (f.stalkMap x)).hom).mapHomologicalComplex c).obj K).d n m :=
  (((openRestrictionComplexIso f x c).app K).hom.comm n m).symm

end AlgebraicGeometry.Scheme.Modules.Stalk
