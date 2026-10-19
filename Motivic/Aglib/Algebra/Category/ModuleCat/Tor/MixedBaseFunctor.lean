/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.MixedBase
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Naturality of the mixed-base comparison

The constructed comparison is a genuine natural isomorphism of the two
curried module bifunctors. Its naturality simultaneously treats both inputs.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TensorProduct
open scoped ChangeOfRings ModuleCat.TorComparison.ExteriorModule

universe u

namespace ModuleCat.TorComparison.MixedBase

variable (k U V Q : Type u) [CommRing k] [CommRing U] [CommRing V] [CommRing Q]
  [Algebra k U] [Algebra k V] (μ : U ⊗[k] V →+* Q)

/-- Extension of the exterior bifunctor along the specified ambient map. -/
def sourceBifunctor : ModuleCat.{u} U ⥤ ModuleCat.{u} V ⥤ ModuleCat.{u} Q :=
  ExteriorModule.bifunctor k U V ⋙
    (Functor.whiskeringRight (ModuleCat.{u} V) (ModuleCat.{u} (U ⊗[k] V)) (ModuleCat.{u} Q)).obj
      (ModuleCat.extendScalars μ)

/-- Tensoring the two actual scalar extension functors over the common ring. -/
def targetBifunctor : ModuleCat.{u} U ⥤ ModuleCat.{u} V ⥤ ModuleCat.{u} Q :=
  ModuleCat.extendScalars (leftMap k U V Q μ) ⋙ curriedTensor (ModuleCat.{u} Q) ⋙
    (Functor.whiskeringLeft (ModuleCat.{u} V) (ModuleCat.{u} Q) (ModuleCat.{u} Q)).obj
      (ModuleCat.extendScalars (rightMap k U V Q μ))

variable {k U V Q}

/-- The actual scalar-extended exterior map in both inputs. -/
def sourceMap {M M' : ModuleCat.{u} U} {N N' : ModuleCat.{u} V}
    (f : M ⟶ M') (g : N ⟶ N') : source k U V Q μ M N ⟶ source k U V Q μ M' N' :=
  (ModuleCat.extendScalars μ).map (ExteriorModule.hom k f g)

/-- The tensor of the two scalar-extended input maps. -/
def targetMap {M M' : ModuleCat.{u} U} {N N' : ModuleCat.{u} V}
    (f : M ⟶ M') (g : N ⟶ N') : target k U V Q μ M N ⟶ target k U V Q μ M' N' :=
  ModuleCat.ofHom (TensorProduct.map
    ((ModuleCat.extendScalars (leftMap k U V Q μ)).map f).hom
    ((ModuleCat.extendScalars (rightMap k U V Q μ)).map g).hom)

/-- The constructed isomorphism commutes with both module maps simultaneously. -/
theorem iso_naturality {M M' : ModuleCat.{u} U} {N N' : ModuleCat.{u} V}
    (f : M ⟶ M') (g : N ⟶ N') :
    sourceMap μ f g ≫ (iso μ M' N').hom = (iso μ M N).hom ≫ targetMap μ f g := by
  apply ModuleCat.hom_ext
  apply source_ext μ M N
  intro q m n
  rfl

/-- The actual mixed-base natural isomorphism of curried bifunctors. -/
def bifunctorIso : sourceBifunctor k U V Q μ ≅ targetBifunctor k U V Q μ :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun N ↦ iso μ M N) (by
    intro N N' g
    apply ModuleCat.hom_ext
    apply source_ext μ M N
    intro q m n
    rfl)) (by
    intro M M' f
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    apply source_ext μ M N
    intro q m n
    rfl)

end ModuleCat.TorComparison.MixedBase
