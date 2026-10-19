/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Pushforward.Affine.FiniteAlgebra
public import Motivic.Aglib.Algebra.Homology.LengthEuler.FiniteAlgebra
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Actual whole-algebra pushforward complex consumers

Arbitrary quotient complexes exercise the natural chain and homology comparisons.
The numerical consumer derives finite homology of the actual pushforward stalk
from only the whole local coefficient complex, and sums all its maximal branches.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.AffinePushforwardFiniteAlgebra
open _root_.AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward.Affine
open _root_.HomologicalComplex.ModuleLengthEuler

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A : CommRingCat.{u}) (I : Ideal A) (p : PrimeSpectrum A)

local instance quotientTilde_additive :
    (tilde.functor (CommRingCat.of (A ⧸ I))).Additive :=
  AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor

/-- Every original quotient complex, with no boundedness or length hypothesis,
is compared to restriction of its whole local coefficient complex. -/
def quotientComplexIso (K : ChainComplex (ModuleCat.{u} (A ⧸ I)) ℕ) :
    (((tilde.functor (CommRingCat.of (A ⧸ I)) ⋙
      Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ⋙
        Stalk.functor (X := Spec A) p).mapHomologicalComplex _).obj K ≅
      ((ModuleCat.extendScalars
          (algebraMap (A ⧸ I) (wholeStalkAlgebra A (.of (A ⧸ I)) p)) ⋙
        ModuleCat.restrictScalars
          (algebraMap ((Spec A).presheaf.stalk p)
            (wholeStalkAlgebra A (.of (A ⧸ I)) p))).mapHomologicalComplex _).obj K :=
  (pushforwardStalkWholeAlgebraComplexIso A (.of (A ⧸ I)) p _).app K

/-- Actual quotient pushforward homology is compared in every degree. -/
def quotientHomologyIso (K : ChainComplex (ModuleCat.{u} (A ⧸ I)) ℕ) (n : ℕ) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (quotientComplexIso A I p K)

/-- The quotient example retains every original higher differential. -/
theorem quotient_differential_square (K : ChainComplex (ModuleCat.{u} (A ⧸ I)) ℕ)
    (i j : ℕ) :
    ((quotientComplexIso A I p K).hom.f i) ≫
        (((ModuleCat.extendScalars
            (algebraMap (A ⧸ I) (wholeStalkAlgebra A (.of (A ⧸ I)) p)) ⋙
          ModuleCat.restrictScalars
            (algebraMap ((Spec A).presheaf.stalk p)
              (wholeStalkAlgebra A (.of (A ⧸ I)) p))).mapHomologicalComplex _).obj K).d i j =
      ((((tilde.functor (CommRingCat.of (A ⧸ I)) ⋙
        Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ⋙
          Stalk.functor (X := Spec A) p).mapHomologicalComplex _).obj K).d i j ≫
        ((quotientComplexIso A I p K).hom.f j) :=
  (quotientComplexIso A I p K).hom.comm i j

variable (B : CommRingCat.{u}) [Algebra A B] [Module.Finite A B]
  [IsNoetherianRing ((Spec A).presheaf.stalk p)]

local instance sourceTilde_additive : (tilde.functor B).Additive :=
  AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor

/-- Finite homology only of the whole local coefficient complex yields the
actual pushforward-stalk Euler sum over all maximal branches. -/
theorem actualPushforwardEuler (K : ChainComplex (ModuleCat.{u} B) ℕ) (sign : ℕ → ℤ)
    (hK : FiniteHomology (((ModuleCat.extendScalars
      (algebraMap B (wholeStalkAlgebra A B p))).mapHomologicalComplex _).obj K)) :
    let C := (((tilde.functor B ⋙ Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))) ⋙
        Stalk.functor (X := Spec A) p).mapHomologicalComplex _).obj K
    ∃ hC : FiniteHomology C, homologyEuler C sign hC =
      finiteAlgebraFiberEuler ((Spec A).presheaf.stalk p) (wholeStalkAlgebra A B p)
        (((ModuleCat.extendScalars
          (algebraMap B (wholeStalkAlgebra A B p))).mapHomologicalComplex _).obj K) sign hK := by
  let L := ((ModuleCat.extendScalars
    (algebraMap B (wholeStalkAlgebra A B p))).mapHomologicalComplex _).obj K
  let e := (pushforwardStalkWholeAlgebraComplexIso A B p (ComplexShape.down ℕ)).app K
  have hL := hK.finiteAlgebra_restrict ((Spec A).presheaf.stalk p)
    (wholeStalkAlgebra A B p) L
  have hC := hL.of_quasiIso e.inv
  refine ⟨hC, ?_⟩
  exact (homologyEuler_eq_of_quasiIso e.hom sign hC hL).trans
    (homologyEuler_finiteAlgebra_eq_fiberEuler ((Spec A).presheaf.stalk p)
      (wholeStalkAlgebra A B p) L sign hK)

end Motivic.MotivicTest.AffinePushforwardFiniteAlgebra
