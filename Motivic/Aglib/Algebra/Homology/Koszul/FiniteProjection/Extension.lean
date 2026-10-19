/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.FiniteProjection.Tensor
public import Mathlib.RingTheory.Flat.Localization

/-!
# Scalar extension of arbitrary-complex finite Koszul tensors

An additive cross-ring functor preserving the specified scalar multiplications
commutes naturally with a finite Koszul tensor. Scalar extension satisfies
this compatibility for every ring map, giving a literal chain isomorphism
without flatness. The homology comparison separately requires a flat map and
composes the already proved scalar-extension homology isomorphism. Localization
is an explicit flat specialization, not an assumption of general exactness.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings

namespace ChainComplex.Koszul

variable {R S : Type u} [CommRing R] [CommRing S]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the genuine one-equation cross-ring comparison. -/
def singleTensorCrossMapNatIso (F : ModuleCat R ⥤ ModuleCat S) [F.Additive]
    (a : R) (b : S)
    (hab : ∀ X : ModuleCat R, F.map (ModuleCat.ofHom (LinearMap.lsmul R X a)) =
      ModuleCat.ofHom (LinearMap.lsmul S (F.obj X) b)) :
    singleTensorFunctor a ⋙ F.mapHomologicalComplex (ComplexShape.down ℕ) ≅
      F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙ singleTensorFunctor b :=
  NatIso.ofComponents (fun K => singleTensorCrossMapIso F a b K hab) (by
    intro K L g
    apply HomologicalComplex.Hom.ext
    funext n
    change F.map (((singleComplex R a) ◁ g).f n) ≫ singleTensorCrossMapToX F a b L n =
      singleTensorCrossMapToX F a b K n ≫
        (((singleComplex S b) ◁ (F.mapHomologicalComplex (ComplexShape.down ℕ)).map g).f n)
    cases n with
    | zero =>
      apply crossMappedSingleTensor_hom_ext_zero F a K
      rw [← Category.assoc, ← Functor.map_comp, singleTensorιZero_naturality,
        Functor.map_comp, Category.assoc, crossMappedιZero_singleTensorCrossMapToX]
      rw [← Category.assoc, crossMappedιZero_singleTensorCrossMapToX,
        singleTensorιZero_naturality]
      rfl
    | succ n =>
      apply crossMappedSingleTensor_hom_ext F a K n
      · rw [← Category.assoc, ← Functor.map_comp, singleTensorιZero_naturality,
          Functor.map_comp, Category.assoc, crossMappedιZero_singleTensorCrossMapToX]
        rw [← Category.assoc, crossMappedιZero_singleTensorCrossMapToX,
          singleTensorιZero_naturality]
        rfl
      · rw [← Category.assoc, ← Functor.map_comp, singleTensorιOne_naturality,
          Functor.map_comp, Category.assoc, crossMappedιOne_singleTensorCrossMapToX]
        rw [← Category.assoc, crossMappedιOne_singleTensorCrossMapToX,
          singleTensorιOne_naturality]
        rfl)

/-- Finite-list cross-ring comparison for an actual additive scalar-compatible functor. -/
def koszulTensorCrossMapNatIso (F : ModuleCat R ⥤ ModuleCat S) [F.Additive]
    (f : R →+* S)
    (hF : ∀ (a : R) (X : ModuleCat R), F.map (ModuleCat.ofHom (LinearMap.lsmul R X a)) =
      ModuleCat.ofHom (LinearMap.lsmul S (F.obj X) (f a))) : (s : List R) →
    koszulTensorFunctor s ⋙ F.mapHomologicalComplex (ComplexShape.down ℕ) ≅
      F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙ koszulTensorFunctor (s.map f)
  | [] =>
      Functor.isoWhiskerRight (leftUnitorNatIso (ChainComplex (ModuleCat R) ℕ))
          (F.mapHomologicalComplex (ComplexShape.down ℕ)) ≪≫
        Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm ≪≫
        Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.down ℕ))
          (leftUnitorNatIso (ChainComplex (ModuleCat S) ℕ)).symm
  | a :: s =>
      Functor.isoWhiskerRight (tensorLeftTensor (singleComplex R a) (chainComplex s))
          (F.mapHomologicalComplex (ComplexShape.down ℕ)) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (koszulTensorFunctor s)
          (singleTensorCrossMapNatIso F a (f a) (hF a)) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (koszulTensorCrossMapNatIso F f hF s)
          (singleTensorFunctor (f a)) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.down ℕ))
          (tensorLeftTensor (singleComplex S (f a)) (chainComplex (s.map f))).symm

/-- The literal termwise scalar-extension functor on nonnegative complexes. -/
abbrev extendChainFunctor (f : R →+* S) :
    ChainComplex (ModuleCat R) ℕ ⥤ ChainComplex (ModuleCat S) ℕ :=
  (ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.down ℕ)

/-- Scalar extension sends multiplication by a source scalar to multiplication
by its actual image, without any flatness assumption. -/
theorem extendScalars_map_lsmul (f : R →+* S) (a : R) (M : ModuleCat R) :
    (ModuleCat.extendScalars f).map (ModuleCat.ofHom (LinearMap.lsmul R M a)) =
      ModuleCat.ofHom (LinearMap.lsmul S ((ModuleCat.extendScalars f).obj M) (f a)) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  let := f.toAlgebra
  change (1 : S) ⊗ₜ[R] (a • m) = f a • ((1 : S) ⊗ₜ[R] m)
  rw [← TensorProduct.smul_tmul]
  simp only [Algebra.smul_def, mul_one, TensorProduct.smul_tmul']
  rfl

/-- Scalar extension commutes naturally with finite Koszul tensoring for every ring map. -/
def koszulTensorExtendNatIso (f : R →+* S) (s : List R) :
    koszulTensorFunctor s ⋙ extendChainFunctor f ≅
      extendChainFunctor f ⋙ koszulTensorFunctor (s.map f) :=
  koszulTensorCrossMapNatIso (ModuleCat.extendScalars f) f (extendScalars_map_lsmul f) s

/-- The literal finite-list scalar-extension chain comparison for an arbitrary complex. -/
def koszulTensorExtendIso (f : R →+* S) (s : List R)
    (K : ChainComplex (ModuleCat R) ℕ) :
    crossMappedComplex (ModuleCat.extendScalars f)
        (HomologicalComplex.tensorObj (chainComplex s) K) ≅
      HomologicalComplex.tensorObj (chainComplex (s.map f))
        (crossMappedComplex (ModuleCat.extendScalars f) K) :=
  (koszulTensorExtendNatIso f s).app K

/-- The extension comparison is natural for every actual chain map. -/
theorem koszulTensorExtendIso_naturality (f : R →+* S) (s : List R)
    {K L : ChainComplex (ModuleCat R) ℕ} (g : K ⟶ L) :
    (extendChainFunctor f).map ((koszulTensorFunctor s).map g) ≫
        (koszulTensorExtendIso f s L).hom =
      (koszulTensorExtendIso f s K).hom ≫
        (koszulTensorFunctor (s.map f)).map ((extendChainFunctor f).map g) :=
  (koszulTensorExtendNatIso f s).hom.naturality g

/-- The component square contains the actual differentials, extended termwise. -/
theorem koszulTensorExtendIso_hom_comm (f : R →+* S) (s : List R)
    (K : ChainComplex (ModuleCat R) ℕ) (i j : ℕ) :
    (koszulTensorExtendIso f s K).hom.f i ≫
        (HomologicalComplex.tensorObj (chainComplex (s.map f))
          (crossMappedComplex (ModuleCat.extendScalars f) K)).d i j =
      (ModuleCat.extendScalars f).map
          ((HomologicalComplex.tensorObj (chainComplex s) K).d i j) ≫
        (koszulTensorExtendIso f s K).hom.f j :=
  (koszulTensorExtendIso f s K).hom.comm i j

/-- Flatness is required only here, to commute actual homology with extension. -/
def flatKoszulTensorExtendHomologyIso (f : R →+* S) (hf : f.Flat) (s : List R)
    (K : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    (ModuleCat.extendScalars f).obj
        ((HomologicalComplex.tensorObj (chainComplex s) K).homology n) ≅
      (HomologicalComplex.tensorObj (chainComplex (s.map f))
        (crossMappedComplex (ModuleCat.extendScalars f) K)).homology n :=
  _root_.ModuleCat.TorComparison.flatExtendHomologyIso f hf
      (HomologicalComplex.tensorObj (chainComplex s) K) n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) n).mapIso
      (koszulTensorExtendIso f s K)

/-- Localization supplies its actual flatness for the finite-list homology comparison. -/
def localizationKoszulTensorHomologyIso [Algebra R S] (U : Submonoid R) [IsLocalization U S]
    (s : List R) (K : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    (ModuleCat.extendScalars (algebraMap R S)).obj
        ((HomologicalComplex.tensorObj (chainComplex s) K).homology n) ≅
      (HomologicalComplex.tensorObj (chainComplex (s.map (algebraMap R S)))
        (crossMappedComplex (ModuleCat.extendScalars (algebraMap R S)) K)).homology n :=
  flatKoszulTensorExtendHomologyIso (algebraMap R S)
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S U)) s K n

end ChainComplex.Koszul
