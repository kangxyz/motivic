/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.ExteriorResolution
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! Consumers of the actual exterior-algebra projective resolution. -/

@[expose] public section

open CategoryTheory HomologicalComplex
open scoped TensorProduct
open scoped ModuleCat.TorComparison.ExteriorModule

universe u

namespace Motivic.MotivicTest.TorComparisonExteriorResolution

variable {k U V : Type u} [Field k] [CommRing U] [CommRing V]
  [Algebra k U] [Algebra k V]

attribute [local instance] _root_.ModuleCat.TorComparison.ExteriorModule.baseModule
  _root_.ModuleCat.TorComparison.ExteriorModule.baseScalarTower

/-- The resolved target carries the literal action of both exterior algebra factors. -/
theorem targetExteriorAction (M : ModuleCat.{u} U) (N : ModuleCat.{u} V)
    (a : U) (b : V) (m : M) (n : N) :
    (a ⊗ₜ[k] b) • (m ⊗ₜ[k] n : _root_.ModuleCat.TorComparison.ExteriorModule.obj k U V M N) =
      (a • m) ⊗ₜ[k] (b • n) := rfl

/-- Arbitrary algebra resolutions yield a genuine resolution over the tensor algebra. -/
noncomputable def arbitraryExteriorResolution
    {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    ProjectiveResolution (_root_.ModuleCat.TorComparison.ExteriorModule.obj k U V M N) :=
  _root_.ModuleCat.TorComparison.exteriorProjectiveResolution P Q

/-- Projectivity is over the full exterior algebra in every total degree. -/
theorem ambientTermProjective
    {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) (n : ℕ) :
    Projective ((mapBifunctor P.complex Q.complex
      (_root_.ModuleCat.TorComparison.ExteriorModule.bifunctor k U V) (ComplexShape.down ℕ)).X n) :=
  (_root_.ModuleCat.TorComparison.exteriorProjectiveResolution (k := k) P Q).projective n

/-- Positive exactness holds in the full exterior-algebra module category. -/
theorem ambientPositiveExact
    {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) (n : ℕ) :
    (mapBifunctor P.complex Q.complex
      (_root_.ModuleCat.TorComparison.ExteriorModule.bifunctor k U V) (ComplexShape.down ℕ)).ExactAt
          (n + 1) :=
  _root_.ModuleCat.TorComparison.exteriorProjectiveResolution_exactAt_succ P Q n

/-- The actual constructed augmentation is a quasi-isomorphism. -/
theorem ambientAugmentationQuasiIso
    {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    QuasiIso (_root_.ModuleCat.TorComparison.exteriorProjectiveResolution (k := k) P Q).π :=
  (_root_.ModuleCat.TorComparison.exteriorProjectiveResolution (k := k) P Q).quasiIso

/-- The augmentation is literally the total map of the given augmentations followed
by the canonical single-complex identification. -/
theorem literalAugmentation
    {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    (_root_.ModuleCat.TorComparison.exteriorProjectiveResolution (k := k) P Q).π =
      mapBifunctorMap P.π Q.π (_root_.ModuleCat.TorComparison.ExteriorModule.bifunctor k U V)
        (ComplexShape.down ℕ) ≫
      (exteriorSingleIso (_root_.ModuleCat.TorComparison.ExteriorModule.bifunctor k U V) M N).hom :=
  rfl

/-- The actual total differential is compatible with the constructed augmentation. -/
theorem totalDifferentialAugmentationZero
    {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    (_root_.ModuleCat.TorComparison.exteriorProjectiveResolution (k := k) P Q).complex.d 1 0 ≫
      (_root_.ModuleCat.TorComparison.exteriorProjectiveResolution (k := k) P Q).π.f 0 = 0 :=
  (_root_.ModuleCat.TorComparison.exteriorProjectiveResolution (k := k) P Q).complex_d_comp_π_f_zero

/-- In particular, arbitrary ideal quotients are admitted as correspondence supports;
there is no flatness or regularity hypothesis on either ideal. -/
noncomputable def quotientSupportResolution (I : Ideal U) (J : Ideal V) :
    ProjectiveResolution
      (_root_.ModuleCat.TorComparison.ExteriorModule.obj k U V (ModuleCat.of U (U ⧸ I))
        (ModuleCat.of V (V ⧸ J))) :=
  _root_.ModuleCat.TorComparison.exteriorProjectiveResolution
    (projectiveResolution (ModuleCat.of U (U ⧸ I)))
    (projectiveResolution (ModuleCat.of V (V ⧸ J)))

end Motivic.MotivicTest.TorComparisonExteriorResolution
