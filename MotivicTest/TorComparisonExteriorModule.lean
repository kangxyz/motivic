/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.ExteriorModuleTotal

/-! Real consumers of the full exterior-algebra module and projectivity API. -/

@[expose] public section

noncomputable section

open CategoryTheory TensorProduct
open Motivic.TorComparison
open scoped Motivic.TorComparison.ExteriorModule

universe u

namespace Motivic.MotivicTest.TorComparisonExteriorModule

variable (k U V M N : Type u) [CommRing k] [CommRing U] [CommRing V]
  [Algebra k U] [Algebra k V]
  [AddCommGroup M] [Module k M] [Module U M] [IsScalarTower k U M]
  [AddCommGroup N] [Module k N] [Module V N] [IsScalarTower k V N]

/-- Both algebra factors occur in the literal action. -/
theorem scalar_formula (a : U) (b : V) (m : M) (n : N) :
    (a ⊗ₜ[k] b) • (m ⊗ₜ[k] n) = (a • m) ⊗ₜ[k] (b • n) :=
  ExteriorModule.smul_tmul a b m n

/-- Projectivity is over the exterior algebra, with no base-projectivity assumption. -/
theorem exterior_projective [Module.Projective U M] [Module.Projective V N] :
    Module.Projective (U ⊗[k] V) (M ⊗[k] N) :=
  ExteriorModule.projective k U V M N

/-- The categorical projectivity conclusion has the same full scalar ring. -/
theorem category_projective [Module.Projective U M] [Module.Projective V N] :
    CategoryTheory.Projective (ModuleCat.of (U ⊗[k] V) (M ⊗[k] N)) :=
  ExteriorModule.categorical_projective k U V M N

/-- Tensoring identity maps really gives the exterior identity. -/
theorem identity_map :
    ExteriorModule.map (k := k) (LinearMap.id : M →ₗ[U] M)
      (LinearMap.id : N →ₗ[V] N) = LinearMap.id :=
  ExteriorModule.map_id

/-- Coefficients of the explicit free equivalence are genuine algebra tensors. -/
theorem free_coefficients {ι κ : Type u} (f : ι →₀ U) (g : κ →₀ V) (i : ι) (j : κ) :
    ExteriorModule.freeTensorEquiv k U V ι κ (f ⊗ₜ[k] g) (i, j) = f i ⊗ₜ[k] g j :=
  ExteriorModule.freeTensorEquiv_tmul_apply k U V f g i j

/-- Projective objects remain projective under the actual curried exterior functor. -/
theorem functor_projective (X : ModuleCat.{u} U) (Y : ModuleCat.{u} V)
    [CategoryTheory.Projective X] [CategoryTheory.Projective Y] :
    CategoryTheory.Projective (((ExteriorModule.bifunctor k U V).obj X).obj Y) :=
  ExteriorModule.projective_obj k U V X Y

/-- Additivity of the first slot is available to total-complex constructions. -/
theorem additive_left : (ExteriorModule.bifunctor k U V).Additive := inferInstance

/-- Additivity of the second slot is available to total-complex constructions. -/
theorem additive_right (X : ModuleCat.{u} U) :
    ((ExteriorModule.bifunctor k U V).obj X).Additive := inferInstance

attribute [local instance] ExteriorModule.baseModule ExteriorModule.baseScalarTower

/-- Restriction of the exterior object gives the original base tensor module. -/
def restrictTensor (X : ModuleCat.{u} U) (Y : ModuleCat.{u} V) :
    (ModuleCat.restrictScalars (algebraMap k (U ⊗[k] V))).obj (ExteriorModule.obj k U V X Y) ≅
      ModuleCat.of k (X ⊗[k] Y) :=
  ExteriorModule.restrictObjIso k U V X Y

/-- Actual nonnegative exterior total terms are projective over the full ambient algebra. -/
theorem total_terms (F : ChainComplex (ModuleCat.{u} U) ℕ)
    (G : ChainComplex (ModuleCat.{u} V) ℕ)
    [∀ i, CategoryTheory.Projective (F.X i)] [∀ i, CategoryTheory.Projective (G.X i)] (n : ℕ) :
    CategoryTheory.Projective
      ((HomologicalComplex.mapBifunctor F G (ExteriorModule.bifunctor k U V)
        (ComplexShape.down ℕ)).X n) :=
  ExteriorModule.projective_total_X k U V (ComplexShape.down ℕ) F G n

end Motivic.MotivicTest.TorComparisonExteriorModule
