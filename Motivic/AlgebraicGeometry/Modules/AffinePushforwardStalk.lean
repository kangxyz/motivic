/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.AffinePushforwardTilde
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Scalar-compatible affine pushforward stalks

Stalks of sheaves of modules are taken with their actual structure-stalk action.
The affine tilde and pushforward comparisons are transported through this action,
so that localization comparisons can be used for actual stalk complexes.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Motivic.ModuleStalk

variable {X : Scheme.{u}} (x : X)

/-- The canonical presheaf-module stalk action, exposed for scheme modules. -/
instance stalkModule (M : X.Modules) :
    Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) M.val x

/-- The same canonical action on the object spelling used by the ordinary stalk functor. -/
instance stalkFunctorModule (M : X.Modules) :
    Module (X.presheaf.stalk x)
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj M.presheaf) :=
  stalkModule x M

/-- Actual sheaf-module stalk maps respect multiplication by every structure-stalk element. -/
theorem stalkMap_smul {M N : X.Modules} (φ : M ⟶ N)
    (r : X.presheaf.stalk x) (m : M.presheaf.stalk x) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.mapPresheaf (r • m) =
      r • (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.mapPresheaf m := by
  obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hxV, m, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
  rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV r]
  erw [← PresheafOfModules.germ_smul (R := X.presheaf) M.val x V hxV]
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.mapPresheaf
      (M.presheaf.germ V x hxV (X.presheaf.map (homOfLE hVU).op r • m)) =
    X.presheaf.germ V x hxV (X.presheaf.map (homOfLE hVU).op r) •
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.mapPresheaf
        (M.presheaf.germ V x hxV m)
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change N.presheaf.germ V x hxV
    (φ.app V (X.presheaf.map (homOfLE hVU).op r • m)) = _
  erw [φ.app_smul, PresheafOfModules.germ_smul (R := X.presheaf) N.val]
  rfl

/-- The actual stalk map of a sheaf-module morphism as a structure-stalk-linear morphism. -/
def map {M N : X.Modules} (φ : M ⟶ N) :
    ModuleCat.of (X.presheaf.stalk x) (M.presheaf.stalk x) ⟶
      ModuleCat.of (X.presheaf.stalk x) (N.presheaf.stalk x) :=
  ModuleCat.ofHom
    { __ := ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.mapPresheaf).hom
      map_smul' := stalkMap_smul x φ }

/-- The functor taking a sheaf module to its actual structure-stalk module. -/
def functor : X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) where
  obj M := ModuleCat.of (X.presheaf.stalk x) (M.presheaf.stalk x)
  map := map x
  map_id M := by
    ext m
    exact ConcreteCategory.congr_hom
      ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_id M) m
  map_comp φ ψ := by
    ext m
    exact ConcreteCategory.congr_hom
      ((Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp φ ψ) m

instance functor_additive : (functor x).Additive where
  map_add {M N} {φ ψ} := by
    ext m
    exact ConcreteCategory.congr_hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_add
        (f := φ.mapPresheaf) (g := ψ.mapPresheaf)) m

end Motivic.ModuleStalk

namespace Motivic.AffinePushforward

open scoped TensorProduct

variable (A : CommRingCat.{u}) (p : PrimeSpectrum A) (M : ModuleCat.{u} A)

/-- The canonical coordinate-ring algebra structure on the actual affine structure stalk. -/
instance structureStalkAlgebra : Algebra A ((Spec A).presheaf.stalk p) :=
  inferInstanceAs (Algebra A ((structurePresheafInCommRingCat A).stalk p))

/-- The structure stalk is the localization of the original coordinate ring at its actual prime. -/
instance structureStalk_isLocalization :
    IsLocalization p.asIdeal.primeCompl ((Spec A).presheaf.stalk p) :=
  inferInstanceAs
    (IsLocalization p.asIdeal.primeCompl ((structurePresheafInCommRingCat A).stalk p))

/-- The canonical sheaf-stalk action specialized to an affine tilde module. -/
instance tildeStalkModule :
    Module ((Spec A).presheaf.stalk p) ((tilde M).presheaf.stalk p) :=
  ModuleStalk.stalkModule (X := Spec A) p (tilde M)

/-- The coordinate-ring and actual structure-stalk actions on a tilde stalk agree. -/
instance tildeStalk_isScalarTower :
    IsScalarTower A ((Spec A).presheaf.stalk p) ((tilde M).presheaf.stalk p) :=
  inferInstanceAs (IsScalarTower A ((structurePresheafInCommRingCat A).stalk p)
    ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf A M).presheaf p))

set_option backward.isDefEq.respectTransparency false in
/-- The actual tilde stalk is scalar extension to the actual structure stalk.
Its linearity uses the canonical sheaf-stalk action, rather than a transported
replacement action. -/
def tildeStalkTensorEquiv :
    (Spec A).presheaf.stalk p ⊗[A] M ≃ₗ[(Spec A).presheaf.stalk p]
      (tilde M).presheaf.stalk p :=
  (IsLocalizedModule.isBaseChange p.asIdeal.primeCompl ((Spec A).presheaf.stalk p)
    (tilde.toStalk M p).hom).equiv

/-- The tensor comparison sends a pure tensor to the actual scalar action on a germ. -/
@[simp]
theorem tildeStalkTensorEquiv_tmul (r : (Spec A).presheaf.stalk p) (m : M) :
    tildeStalkTensorEquiv A p M (r ⊗ₜ[A] m) = r • tilde.toStalk M p m :=
  IsBaseChange.equiv_tmul _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map into a tilde stalk is natural in the original module. -/
theorem tilde_toStalk_naturality {M N : ModuleCat.{u} A} (g : M ⟶ N) (m : M) :
    ModuleStalk.map p (tilde.map g) (tilde.toStalk M p m) = tilde.toStalk N p (g m) := by
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).map (tilde.map g).mapPresheaf
      ((tilde M).presheaf.germ ⊤ p (by trivial) (tilde.toOpen M ⊤ m)) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change (tilde N).presheaf.germ ⊤ p (by trivial)
      (((modulesSpecToSheaf.map (tilde.map g)).hom.app (.op ⊤)) (tilde.toOpen M ⊤ m)) = _
  rw [← ModuleCat.comp_apply, tilde.toOpen_map_app, ModuleCat.comp_apply]
  rfl

/-- The O-stalk-linear tensor comparison respects every actual module map. -/
theorem tildeStalkTensorEquiv_naturality {M N : ModuleCat.{u} A} (g : M ⟶ N)
    (z : (Spec A).presheaf.stalk p ⊗[A] M) :
    ModuleStalk.map p (tilde.map g) (tildeStalkTensorEquiv A p M z) =
      tildeStalkTensorEquiv A p N ((g.hom.baseChange ((Spec A).presheaf.stalk p)) z) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul r m =>
    simp only [LinearMap.baseChange_tmul, tildeStalkTensorEquiv_tmul, map_smul]
    exact congrArg (r • ·) (tilde_toStalk_naturality A p g m)

/-- Literal tensor extension from the affine coordinate ring to its actual structure stalk. -/
def stalkTensorFunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} ((Spec A).presheaf.stalk p) where
  obj M := ModuleCat.of _ ((Spec A).presheaf.stalk p ⊗[A] M)
  map g := ModuleCat.ofHom (g.hom.baseChange ((Spec A).presheaf.stalk p))
  map_id M := by ext; rfl
  map_comp g h := by ext; rfl

instance stalkTensorFunctor_additive : (stalkTensorFunctor A p).Additive where
  map_add {M N} {g h} := by
    ext z
    change ((g.hom + h.hom).baseChange _ z) = g.hom.baseChange _ z + h.hom.baseChange _ z
    simp only [LinearMap.baseChange_add, LinearMap.add_apply]

/-- The actual tilde stalk and literal tensor extension are naturally isomorphic. -/
def tildeStalkIso :
    stalkTensorFunctor A p ≅ tilde.functor A ⋙ ModuleStalk.functor (X := Spec A) p :=
  NatIso.ofComponents (fun M => (tildeStalkTensorEquiv A p M).toModuleIso) (fun g => by
    ext z
    exact (tildeStalkTensorEquiv_naturality A p g z).symm)

/-- The affine pushforward stalk comparison is linear over the actual target structure stalk. -/
def pushforwardStalkIso {B : CommRingCat.{u}} (φ : A ⟶ B) :
    (tilde.functor B ⋙ Scheme.Modules.pushforward (Spec.map φ)) ⋙
        ModuleStalk.functor (X := Spec A) p ≅
      ModuleCat.restrictScalars φ.hom ⋙ stalkTensorFunctor A p :=
  Functor.isoWhiskerRight (tildePushforwardIso φ) (ModuleStalk.functor (X := Spec A) p) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ModuleCat.restrictScalars φ.hom) (tildeStalkIso A p).symm

/-- The same natural comparison applies to actual stalk complexes and all their differentials. -/
def pushforwardStalkComplexIso {B : CommRingCat.{u}} (φ : A ⟶ B)
    {ι : Type*} (c : ComplexShape ι) :
    ((tilde.functor B ⋙ Scheme.Modules.pushforward (Spec.map φ)) ⋙
      ModuleStalk.functor (X := Spec A) p).mapHomologicalComplex c ≅
        (ModuleCat.restrictScalars φ.hom ⋙ stalkTensorFunctor A p).mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex (pushforwardStalkIso A p φ) c

/-- Module maps are compared by the actual structure-stalk-linear morphisms. -/
@[reassoc]
theorem pushforwardStalkIso_naturality {B : CommRingCat.{u}} (φ : A ⟶ B)
    {M N : ModuleCat.{u} B} (g : M ⟶ N) :
    ModuleStalk.map p ((Scheme.Modules.pushforward (Spec.map φ)).map (tilde.map g)) ≫
        (pushforwardStalkIso A p φ).hom.app N =
      (pushforwardStalkIso A p φ).hom.app M ≫
        (stalkTensorFunctor A p).map ((ModuleCat.restrictScalars φ.hom).map g) :=
  (pushforwardStalkIso A p φ).hom.naturality g

/-- The complex comparison uses precisely the module comparison in every degree. -/
theorem pushforwardStalkComplexIso_hom_f {B : CommRingCat.{u}} (φ : A ⟶ B)
    {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex (ModuleCat.{u} B) c) (i : ι) :
    ((pushforwardStalkComplexIso A p φ c).app K).hom.f i =
      (pushforwardStalkIso A p φ).hom.app (K.X i) := rfl

/-- Both actual adjacent stalk differentials commute with the tensor comparison. -/
theorem pushforwardStalkComplexIso_d {B : CommRingCat.{u}} (φ : A ⟶ B)
    {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex (ModuleCat.{u} B) c) (i j : ι) :
    ModuleStalk.map p ((Scheme.Modules.pushforward (Spec.map φ)).map (tilde.map (K.d i j))) ≫
        (pushforwardStalkIso A p φ).hom.app (K.X j) =
      (pushforwardStalkIso A p φ).hom.app (K.X i) ≫
        (stalkTensorFunctor A p).map ((ModuleCat.restrictScalars φ.hom).map (K.d i j)) :=
  pushforwardStalkIso_naturality A p φ (K.d i j)

end Motivic.AffinePushforward
