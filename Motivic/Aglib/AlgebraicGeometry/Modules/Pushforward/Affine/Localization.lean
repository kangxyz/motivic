/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Pushforward.Affine.FiniteAlgebra

/-!
# Original affine coefficient complexes in the prime-localization model

The canonical structure-stalk isomorphism transports the actual pushforward
coefficient functor to the same A_p tensor_A B algebra used by the point and
residue comparisons. All comparisons are natural, including the differentials.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules.Pushforward.Affine

section ChangeBase

variable (A R T : Type u) [CommRing A] [CommRing R] [CommRing T]
  [Algebra A R] [Algebra A T] (e : R ≃ₐ[A] T)

/-- Changing the tensor base by an algebra equivalence preserves the actual
restricted target action. -/
def coordinateTensorRingEquiv (M : ModuleCat.{u} A) :
    (coordinateTensorFunctor A R).obj M ≃ₗ[R]
      (coordinateTensorFunctor A T ⋙ ModuleCat.restrictScalars e.toRingHom).obj M := by
  let E : R ⊗[A] M ≃ₗ[A] T ⊗[A] M :=
    TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl A M)
  refine { E.toAddEquiv with map_smul' := ?_ }
  intro r z
  change E (r • z) = e r • E z
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [smul_add, map_add, hz, hw]
  | tmul t m =>
    change e (r * t) ⊗ₜ[A] m = e r • (e t ⊗ₜ[A] m)
    rw [map_mul]
    rfl

/-- The base-ring equivalence comparison commutes with every coefficient-module map. -/
def coordinateTensorRingIso :
    coordinateTensorFunctor A R ≅
      coordinateTensorFunctor A T ⋙ ModuleCat.restrictScalars e.toRingHom :=
  NatIso.ofComponents (fun M => (coordinateTensorRingEquiv A R T e M).toModuleIso)
    (fun {M N} g => by
      ext z
      induction z using TensorProduct.inductionOn with
      | tmul r m => rfl
      | add z w hz hw => simp only [map_add, hz, hw])

/-- Categorical scalar extension along a canonical scalar tower composes literally. -/
def coordinateExtendCompIso [Algebra R T] [IsScalarTower A R T] :
    ModuleCat.extendScalars (algebraMap A R) ⋙ ModuleCat.extendScalars (algebraMap R T) ≅
      ModuleCat.extendScalars (algebraMap A T) := by
  rw [IsScalarTower.algebraMap_eq A R T]
  exact (ModuleCat.extendScalarsComp (algebraMap A R) (algebraMap R T)).symm

end ChangeBase

section PrimeStalk

variable (A B : CommRingCat.{u}) [Algebra A B] (p : PrimeSpectrum A)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The canonical scheme stalk isomorphism transports the literal tensor functor. -/
def primeStalkTensorIso :
    coordinateTensorFunctor A (Localization.AtPrime p.asIdeal) ≅
      stalkTensorFunctor A p ⋙ ModuleCat.restrictScalars (Spec.stalkIso A p).inv.hom :=
  coordinateTensorRingIso A (Localization.AtPrime p.asIdeal) ((Spec A).presheaf.stalk p)
    (StructureSheaf.stalkIso A p)

/-- The actual pushforward stalk, restricted through its canonical prime-stalk
isomorphism, is restriction of the original coefficient extended to A_p tensor_A B. -/
def pushforwardPrimeStalkIso :
    ((tilde.functor B ⋙ Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))) ⋙
        Stalk.functor (X := Spec A) p) ⋙
          ModuleCat.restrictScalars (Spec.stalkIso A p).inv.hom ≅
      ModuleCat.extendScalars (algebraMap B (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)) ⋙
        ModuleCat.restrictScalars
          (algebraMap (Localization.AtPrime p.asIdeal)
              (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)) :=
  Functor.isoWhiskerRight
      (pushforwardStalkIso A p (CommRingCat.ofHom (algebraMap A B))) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ModuleCat.restrictScalars (algebraMap A B))
      (primeStalkTensorIso A p).symm ≪≫
    wholeAlgebraTensorIso A (Localization.AtPrime p.asIdeal) B ≪≫
    Functor.isoWhiskerRight
      (coordinateTensorExtendIso B (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p)).symm _

end PrimeStalk

end AlgebraicGeometry.Scheme.Modules.Pushforward.Affine
