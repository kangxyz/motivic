/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.AffinePushforwardTilde
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Literal complex consumers of affine tilde pushforward

Arbitrary quotient maps exercise the comparison without a flatness hypothesis.
The complex may have infinite-length terms or unbounded homology; this slice
asserts the natural comparison and its differential squares, not an Euler formula.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.AffinePushforwardTilde

open AffinePushforward

variable (A : Type u) [CommRing A] (I : Ideal A)

local instance targetTilde_additive : (tilde.functor (CommRingCat.of A)).Additive :=
  AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor

local instance sourceTilde_additive : (tilde.functor (CommRingCat.of (A ⧸ I))).Additive :=
  AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor

/-- The actual complex comparison applies to every quotient map and every chain complex. -/
def quotientComplexIso (K : ChainComplex (ModuleCat.{u} (A ⧸ I)) ℕ) :
    ((tilde.functor.{u} (CommRingCat.of (A ⧸ I)) ⋙
      Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅
    ((ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk I) ⋙ tilde.functor.{u} (CommRingCat.of A))
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).obj K :=
  (tildePushforwardComplexIso (CommRingCat.ofHom (Ideal.Quotient.mk I)) _).app K

/-- The comparison identifies homology in every degree of the actual sheaf complexes. -/
def quotientHomologyIso (K : ChainComplex (ModuleCat.{u} (A ⧸ I)) ℕ) (n : ℕ) :
    (((tilde.functor.{u} (CommRingCat.of (A ⧸ I)) ⋙
      Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology n ≅
    (((ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk I) ⋙ tilde.functor.{u} (CommRingCat.of A))
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (quotientComplexIso A I K)

/-- Both adjacent maps are transported, including arbitrary higher differentials. -/
theorem quotient_differential_square (K : ChainComplex (ModuleCat.{u} (A ⧸ I)) ℕ) (i j : ℕ) :
    (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map
        (tilde.map (K.d i j)) ≫
        (tildePushforwardIso (CommRingCat.ofHom (Ideal.Quotient.mk I))).hom.app (K.X j) =
      (tildePushforwardIso (CommRingCat.ofHom (Ideal.Quotient.mk I))).hom.app (K.X i) ≫
        tilde.map ((ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk I)).map (K.d i j)) :=
  tildePushforwardComplexIso_d (CommRingCat.ofHom (Ideal.Quotient.mk I)) _ K i j

end Motivic.MotivicTest.AffinePushforwardTilde
