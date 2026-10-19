/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.ExteriorModule
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The exterior tensor bifunctor

The exterior action and maps are packaged as a curried additive bifunctor into
modules over the full tensor product algebra. All base actions on the input
module categories are induced by the specified algebra maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory TensorProduct
open scoped ModuleCat.TorComparison.ExteriorModule

universe u

namespace ModuleCat.TorComparison.ExteriorModule

variable (k U V : Type u) [CommRing k] [CommRing U] [CommRing V]
  [Algebra k U] [Algebra k V]

/-- The induced base action on an input module. -/
abbrev baseModule (M : ModuleCat.{u} U) : Module k M :=
  Module.compHom M (algebraMap k U)

attribute [local instance] baseModule

/-- The induced base action is compatible with the original algebra action. -/
theorem baseScalarTower (M : ModuleCat.{u} U) : IsScalarTower k U M :=
  IsScalarTower.of_compHom k U M

attribute [local instance] baseScalarTower

/-- Exterior tensor as an object of the actual ambient module category. -/
def obj (M : ModuleCat.{u} U) (N : ModuleCat.{u} V) : ModuleCat.{u} (U ⊗[k] V) :=
  ModuleCat.of (U ⊗[k] V) (M ⊗[k] N)

variable {U V}

/-- Exterior tensor of module-category morphisms. -/
def hom {M M' : ModuleCat.{u} U} {N N' : ModuleCat.{u} V}
    (f : M ⟶ M') (g : N ⟶ N') : obj k U V M N ⟶ obj k U V M' N' :=
  ModuleCat.ofHom (map (k := k) f.hom g.hom)

/-- Pure tensors evaluate functorially. -/
@[simp] theorem hom_tmul {M M' : ModuleCat.{u} U} {N N' : ModuleCat.{u} V}
    (f : M ⟶ M') (g : N ⟶ N') (m : M) (n : N) :
    hom k f g (m ⊗ₜ[k] n) = f m ⊗ₜ[k] g n := rfl

/-- Exterior identity morphisms. -/
@[simp] theorem hom_id (M : ModuleCat.{u} U) (N : ModuleCat.{u} V) :
    hom k (𝟙 M) (𝟙 N) = 𝟙 (obj k U V M N) := by
  apply ModuleCat.hom_ext
  exact map_id

/-- Exterior morphisms preserve composition. -/
theorem hom_comp {M M' M'' : ModuleCat.{u} U} {N N' N'' : ModuleCat.{u} V}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    hom k (f ≫ f') (g ≫ g') = hom k f g ≫ hom k f' g' := by
  apply ModuleCat.hom_ext
  exact map_comp f.hom f'.hom g.hom g'.hom

variable (U V)

/-- The literal exterior tensor bifunctor. -/
def bifunctor : ModuleCat.{u} U ⥤ ModuleCat.{u} V ⥤ ModuleCat.{u} (U ⊗[k] V) where
  obj M :=
    { obj := obj k U V M
      map := fun g ↦ hom k (𝟙 M) g
      map_id := fun N ↦ hom_id k M N
      map_comp := fun g g' ↦ by simpa using hom_comp k (𝟙 M) (𝟙 M) g g' }
  map f :=
    { app := fun N ↦ hom k f (𝟙 N)
      naturality := fun N N' g ↦ by
        rw [← hom_comp, ← hom_comp]
        simp }
  map_id M := by
    apply NatTrans.ext
    funext N
    exact hom_id k M N
  map_comp f f' := by
    apply NatTrans.ext
    funext N
    simpa using hom_comp k f f' (𝟙 N) (𝟙 N)

/-- Additivity in the second input. -/
instance additive_obj (M : ModuleCat.{u} U) : ((bifunctor k U V).obj M).Additive where
  map_add := by
    intro N N' f g
    apply ModuleCat.hom_ext
    change map (k := k) (LinearMap.id : M →ₗ[U] M) (f.hom + g.hom) =
      map (k := k) LinearMap.id f.hom + map (k := k) LinearMap.id g.hom
    ext m n
    simp only [map_tmul, LinearMap.id_apply, LinearMap.add_apply, TensorProduct.tmul_add]

/-- Additivity in the first input. -/
instance additive : (bifunctor k U V).Additive where
  map_add := by
    intro M M' f g
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    change map (k := k) (f.hom + g.hom) (LinearMap.id : N →ₗ[V] N) =
      map (k := k) f.hom LinearMap.id + map (k := k) g.hom LinearMap.id
    ext m n
    simp only [map_tmul, LinearMap.id_apply, LinearMap.add_apply, TensorProduct.add_tmul]

/-- Projectivity of the bifunctor output for projective inputs. -/
theorem projective_obj (M : ModuleCat.{u} U) (N : ModuleCat.{u} V)
    [CategoryTheory.Projective M] [CategoryTheory.Projective N] :
    CategoryTheory.Projective (((bifunctor k U V).obj M).obj N) :=
  categorical_projective k U V M N

/-- Restricting the exterior action gives precisely the original base tensor module. -/
def restrictObjIso (M : ModuleCat.{u} U) (N : ModuleCat.{u} V) :
    (ModuleCat.restrictScalars (algebraMap k (U ⊗[k] V))).obj (obj k U V M N) ≅
      ModuleCat.of k (M ⊗[k] N) :=
  LinearEquiv.toModuleIso
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        change action k U V M N (algebraMap k (U ⊗[k] V) r) x = _
        rw [(action k U V M N).commutes]
        rfl }

/-- The scalar-restriction identification respects both input maps. -/
theorem restrictObjIso_naturality {M M' : ModuleCat.{u} U} {N N' : ModuleCat.{u} V}
    (f : M ⟶ M') (g : N ⟶ N') :
    (ModuleCat.restrictScalars (algebraMap k (U ⊗[k] V))).map (hom k f g) ≫
        (restrictObjIso k U V M' N').hom =
      (restrictObjIso k U V M N).hom ≫
        ModuleCat.ofHom
          (TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k)) := by
  apply ModuleCat.hom_ext
  rfl

end ModuleCat.TorComparison.ExteriorModule
