/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatComplexTensorQuasiIso

/-! Consumers of the actual flat tensor augmentation and double-resolution Tor computation. -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex

universe u

namespace Motivic.MotivicTest.TorComparisonFlatComplexTensor

variable {R : Type u} [CommRing R]

/-- Arbitrary nonnegative quasi-isomorphisms survive a termwise-flat tensor. -/
theorem preserveQuasiIso {A B : ChainComplex (ModuleCat.{u} R) ℕ} (f : A ⟶ B)
    (G : ChainComplex (ModuleCat.{u} R) ℕ) [QuasiIso f] [∀ q, Module.Flat R (G.X q)] :
    QuasiIso (mapBifunctorMap f (𝟙 G) (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)) :=
  _root_.ModuleCat.TorComparison.flatComplexTensor_quasiIso f G

/-- The literal first augmentation of two arbitrary resolutions is a quasi-isomorphism. -/
theorem augmentResolution {M N : ModuleCat.{u} R}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    QuasiIso (mapBifunctorMap P.π (𝟙 Q.complex)
      (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)) :=
  _root_.ModuleCat.TorComparison.tensorProjectiveResolutions_augmentation_quasiIso P Q

/-- Actual Tor is computed from the actual signed total of the two resolutions. -/
noncomputable def actualDoubleResolutionTor {M N : ModuleCat.{u} R}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) (n : ℕ) :
    (mapBifunctor P.complex Q.complex
        (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)).homology n ≅
      (((Tor (ModuleCat R) n).obj M).obj N) :=
  _root_.ModuleCat.TorComparison.tensorProjectiveResolutionsTorIso P Q n

/-- The constructed comparison retains the actual augmentation homology map. -/
theorem actualAugmentationMap {M N : ModuleCat.{u} R}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) (n : ℕ) :
    (actualDoubleResolutionTor P Q n).hom =
      homologyMap (mapBifunctorMap P.π (𝟙 Q.complex)
        (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)) n ≫
          (_root_.ModuleCat.TorComparison.flatComplexTensorSingleTorIso M Q n).hom :=
  _root_.ModuleCat.TorComparison.tensorProjectiveResolutionsTorIso_hom P Q n

end Motivic.MotivicTest.TorComparisonFlatComplexTensor
