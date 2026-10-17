/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.ExteriorModuleFunctor
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Scalar restriction of the actual exterior bicomplex

The exterior tensor bicomplex over `U ⊗[k] V`, after restriction to `k`, is
isomorphic to the ordinary tensor bicomplex of the two restricted complexes.
The isomorphism uses the explicit scalar-compatible module identification and
commutes with both differentials and maps in both complexes. No comparison of
derived functors or augmentation exactness is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
open scoped TensorProduct

universe u

namespace Motivic.TorComparison.ExteriorModule

variable (k U V : Type u) [CommRing k] [CommRing U] [CommRing V]
  [Algebra k U] [Algebra k V]

attribute [local instance] baseModule baseScalarTower

/-- The actual exterior bicomplex before totalization. -/
abbrev exteriorBicomplex (K : ChainComplex (ModuleCat.{u} U) ℕ)
    (L : ChainComplex (ModuleCat.{u} V) ℕ) :=
  (((bifunctor k U V).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj K).obj L

/-- The literal twice-mapped scalar restriction of the exterior bicomplex. -/
abbrev restrictedBicomplex (K : ChainComplex (ModuleCat.{u} U) ℕ)
    (L : ChainComplex (ModuleCat.{u} V) ℕ) :=
  (((ModuleCat.restrictScalars (algebraMap k (U ⊗[k] V))).mapHomologicalComplex
    (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (exteriorBicomplex k U V K L)

/-- The ordinary base tensor bicomplex of the two restricted input complexes. -/
abbrev baseBicomplex (K : ChainComplex (ModuleCat.{u} U) ℕ)
    (L : ChainComplex (ModuleCat.{u} V) ℕ) :=
  (((curriedTensor (ModuleCat.{u} k)).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj
      (((ModuleCat.restrictScalars (algebraMap k U)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K)).obj
      (((ModuleCat.restrictScalars (algebraMap k V)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj L)

/-- Scalar restriction identifies the genuine exterior and base tensor bicomplexes. -/
def scalarBicomplexIso (K : ChainComplex (ModuleCat.{u} U) ℕ)
    (L : ChainComplex (ModuleCat.{u} V) ℕ) :
    restrictedBicomplex k U V K L ≅ baseBicomplex k U V K L :=
  Hom.isoOfComponents
    (fun i ↦ Hom.isoOfComponents
      (fun j ↦ restrictObjIso k U V (K.X i) (L.X j)) (by
        intro j j' _
        apply ModuleCat.hom_ext
        rfl)) (by
      intro i i' _
      ext1 j
      apply ModuleCat.hom_ext
      rfl)

/-- The component identification is the previously constructed scalar module isomorphism. -/
@[simp] theorem scalarBicomplexIso_hom_f_f (K : ChainComplex (ModuleCat.{u} U) ℕ)
    (L : ChainComplex (ModuleCat.{u} V) ℕ) (i j : ℕ) :
    ((scalarBicomplexIso k U V K L).hom.f i).f j =
      (restrictObjIso k U V (K.X i) (L.X j)).hom := rfl

variable {U V}

/-- The exterior bicomplex map induced by both input chain maps. -/
abbrev exteriorBicomplexMap {K K' : ChainComplex (ModuleCat.{u} U) ℕ}
    {L L' : ChainComplex (ModuleCat.{u} V) ℕ} (f : K ⟶ K') (g : L ⟶ L') :
    exteriorBicomplex k U V K L ⟶ exteriorBicomplex k U V K' L' :=
  (((bifunctor k U V).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).map f).app L ≫
  (((bifunctor k U V).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj K').map g

/-- Restrict the actual exterior bicomplex map. -/
abbrev restrictedBicomplexMap {K K' : ChainComplex (ModuleCat.{u} U) ℕ}
    {L L' : ChainComplex (ModuleCat.{u} V) ℕ} (f : K ⟶ K') (g : L ⟶ L') :
    restrictedBicomplex k U V K L ⟶ restrictedBicomplex k U V K' L' :=
  (((ModuleCat.restrictScalars (algebraMap k (U ⊗[k] V))).mapHomologicalComplex
    (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (exteriorBicomplexMap k f g)

/-- The base tensor bicomplex map induced by the two literally restricted chain maps. -/
abbrev baseBicomplexMap {K K' : ChainComplex (ModuleCat.{u} U) ℕ}
    {L L' : ChainComplex (ModuleCat.{u} V) ℕ} (f : K ⟶ K') (g : L ⟶ L') :
    baseBicomplex k U V K L ⟶ baseBicomplex k U V K' L' :=
  (((curriedTensor (ModuleCat.{u} k)).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).map
      (((ModuleCat.restrictScalars (algebraMap k U)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map f)).app
      (((ModuleCat.restrictScalars (algebraMap k V)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj L) ≫
  (((curriedTensor (ModuleCat.{u} k)).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj
      (((ModuleCat.restrictScalars (algebraMap k U)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K')).map
      (((ModuleCat.restrictScalars (algebraMap k V)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map g)

/-- The scalar bicomplex isomorphism is natural in both input complexes. -/
theorem scalarBicomplexIso_naturality {K K' : ChainComplex (ModuleCat.{u} U) ℕ}
    {L L' : ChainComplex (ModuleCat.{u} V) ℕ} (f : K ⟶ K') (g : L ⟶ L') :
    restrictedBicomplexMap k f g ≫ (scalarBicomplexIso k U V K' L').hom =
      (scalarBicomplexIso k U V K L).hom ≫ baseBicomplexMap k f g := by
  ext1 i
  ext1 j
  apply ModuleCat.hom_ext
  rfl

end Motivic.TorComparison.ExteriorModule
