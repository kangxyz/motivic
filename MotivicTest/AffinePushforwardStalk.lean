/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.AffinePushforwardStalk
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Actual O-stalk complex consumers

Every quotient map and every complex are allowed. All maps are linear for the
canonical structure-stalk action, with no finite-length, flatness, or boundedness
premise. Homology is compared only through the constructed chain isomorphism.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Motivic.MotivicTest.AffinePushforwardStalk

open AffinePushforward

variable (A : CommRingCat.{u}) (I : Ideal A) (p : PrimeSpectrum A)

local instance quotientTilde_additive :
    (tilde.functor (CommRingCat.of (A ⧸ I))).Additive :=
  AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor

/-- An arbitrary quotient complex has the actual O-stalk-linear tensor comparison. -/
def quotientComplexIso (K : ChainComplex (ModuleCat.{u} (A ⧸ I)) ℕ) :
    (((tilde.functor (CommRingCat.of (A ⧸ I)) ⋙
      Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ⋙
        ModuleStalk.functor (X := Spec A) p).mapHomologicalComplex _).obj K ≅
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk I) ⋙
        stalkTensorFunctor A p).mapHomologicalComplex _).obj K :=
  (pushforwardStalkComplexIso A p (CommRingCat.ofHom (Ideal.Quotient.mk I)) _).app K

/-- Every degree of actual stalk homology is compared by the literal chain isomorphism. -/
def quotientHomologyIso (K : ChainComplex (ModuleCat.{u} (A ⧸ I)) ℕ) (n : ℕ) :
    ((((tilde.functor (CommRingCat.of (A ⧸ I)) ⋙
      Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ⋙
        ModuleStalk.functor (X := Spec A) p).mapHomologicalComplex _).obj K).homology n ≅
      (((ModuleCat.restrictScalars (Ideal.Quotient.mk I) ⋙
        stalkTensorFunctor A p).mapHomologicalComplex _).obj K).homology n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (quotientComplexIso A I p K)

/-- The comparison transports arbitrary higher differentials as O-stalk-linear maps. -/
theorem quotient_differential_square (K : ChainComplex (ModuleCat.{u} (A ⧸ I)) ℕ)
    (i j : ℕ) :
    ModuleStalk.map p ((Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map (tilde.map (K.d i j))) ≫
        (pushforwardStalkIso A p (CommRingCat.ofHom (Ideal.Quotient.mk I))).hom.app (K.X j) =
      (pushforwardStalkIso A p (CommRingCat.ofHom (Ideal.Quotient.mk I))).hom.app (K.X i) ≫
        (stalkTensorFunctor A p).map ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).map
          (K.d i j)) :=
  pushforwardStalkComplexIso_d A p (CommRingCat.ofHom (Ideal.Quotient.mk I)) _ K i j

/-- The inverse comparison lands in the actual sheaf-stalk action, including nonunits. -/
theorem actual_scalar_action (M : ModuleCat.{u} A) (r : (Spec A).presheaf.stalk p) (m : M) :
    (tildeStalkIso A p).hom.app M (r ⊗ₜ[A] m) = r • tilde.toStalk M p m :=
  tildeStalkTensorEquiv_tmul A p M r m

end Motivic.MotivicTest.AffinePushforwardStalk
