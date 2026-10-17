/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.MixedBaseComplex

/-! # Consumers of the actual mixed-base tensor and total-complex comparison -/

@[expose] public section

noncomputable section

open CategoryTheory TensorProduct
open scoped ChangeOfRings Motivic.TorComparison.ExteriorModule

universe u

namespace Motivic.MotivicTest.TorComparisonMixedBase

open Motivic.TorComparison.MixedBase

attribute [local instance] Motivic.TorComparison.ExteriorModule.baseModule
  Motivic.TorComparison.ExteriorModule.baseScalarTower

variable {k U V Q : Type u} [CommRing k] [CommRing U] [CommRing V] [CommRing Q]
  [Algebra k U] [Algebra k V] (μ : U ⊗[k] V →+* Q)
  (M : ModuleCat.{u} U) (N : ModuleCat.{u} V)

/-- The ordinary comparison is available with only commutative-ring hypotheses. -/
def moduleComparison : source k U V Q μ M N ≅ target k U V Q μ M N := iso μ M N

/-- The forward map uses the specified coefficient and actual induced scalar maps. -/
theorem pure_forward (q : Q) (m : M) (n : N) :
    (moduleComparison μ M N).hom (q ⊗ₜ[U ⊗[k] V,μ] (m ⊗ₜ[k] n)) =
      forwardPure μ M N q m n := rfl

/-- The inverse multiplies coefficients, rather than assuming a target comparison. -/
theorem pure_inverse (q q' : Q) (m : M) (n : N) :
    (moduleComparison μ M N).inv ((q ⊗ₜ[U,leftMap k U V Q μ] m) ⊗ₜ[Q]
      (q' ⊗ₜ[V,rightMap k U V Q μ] n)) =
      (q * q') ⊗ₜ[U ⊗[k] V,μ] (m ⊗ₜ[k] n) := equiv_symm_tmul μ M N q q' m n

/-- The common base action is proved from the tensor-algebra map. -/
theorem base_action (r : k) :
    leftMap k U V Q μ (algebraMap k U r) = rightMap k U V Q μ (algebraMap k V r) :=
  base_compatible μ r

/-- Naturality simultaneously handles both actual input module maps. -/
theorem both_maps {M' : ModuleCat.{u} U} {N' : ModuleCat.{u} V}
    (f : M ⟶ M') (g : N ⟶ N') :
    sourceMap μ f g ≫ (iso μ M' N').hom = (iso μ M N).hom ≫ targetMap μ f g :=
  iso_naturality μ f g

/-- The module comparisons assemble into the actual curried natural isomorphism. -/
def naturalComparison : sourceBifunctor k U V Q μ ≅ targetBifunctor k U V Q μ :=
  bifunctorIso μ

/-- The actual exterior bicomplex is compared with the actual extended-factor bicomplex. -/
def bicomplexComparison (K : ChainComplex (ModuleCat.{u} U) ℕ)
    (L : ChainComplex (ModuleCat.{u} V) ℕ) :
    extendedExteriorBicomplex k U V Q μ K L ≅ extendedFactorsBicomplex k U V Q μ K L :=
  bicomplexIso k U V Q μ K L

/-- The signed total comparison extends the actual exterior total along the actual ring map. -/
def totalComparison (K : ChainComplex (ModuleCat.{u} U) ℕ)
    (L : ChainComplex (ModuleCat.{u} V) ℕ) :
    ((ModuleCat.extendScalars μ).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((Motivic.TorComparison.ExteriorModule.exteriorBicomplex k U V K L).total
          (ComplexShape.down ℕ)) ≅
      (extendedFactorsBicomplex k U V Q μ K L).total (ComplexShape.down ℕ) :=
  totalIso k U V Q μ K L

end Motivic.MotivicTest.TorComparisonMixedBase
