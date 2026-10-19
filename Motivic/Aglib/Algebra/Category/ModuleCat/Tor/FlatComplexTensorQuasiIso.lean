/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatComplexTensorSingle
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.ConeAugmentationCriterion
public import Motivic.Aglib.Algebra.Homology.Bifunctor.TotalCofiber

/-!
# Degreewise-flat nonnegative complexes preserve quasi-isomorphisms

The actual cofiber criterion, the signed cofiber/tensor-total chain
isomorphism, and the proved finite staircase theorem give genuine
quasi-isomorphism preservation. Applying this to a literal resolution
augmentation computes actual one-sided Tor from the tensor total of two
arbitrary projective resolutions. Neither resolved module is assumed flat
or projective, and no balanced-Tor theorem is used.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex

universe u

namespace ModuleCat.TorComparison

variable {R : Type u} [CommRing R]

/-- Tensoring a quasi-isomorphism with a degreewise flat nonnegative complex
preserves quasi-isomorphisms of the literal signed tensor totals. -/
theorem flatComplexTensor_quasiIso
    {A B : ChainComplex (ModuleCat.{u} R) ℕ} (f : A ⟶ B)
    (G : ChainComplex (ModuleCat.{u} R) ℕ) [QuasiIso f]
    [∀ q, Module.Flat R (G.X q)] :
    QuasiIso (mapBifunctorMap f (𝟙 G)
      (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)) := by
  apply quasiIso_of_homotopyCofiber_acyclic
  intro n
  exact (flatComplexTensor_acyclic (homotopyCofiber f) G
    (homotopyCofiber_acyclic_of_quasiIso f) n).of_iso
      (tensorTotalCofiberIso (curriedTensor (ModuleCat R)) f G).symm

/-- A genuine resolution may be literally augmented under a flat complex. -/
theorem flatComplexTensor_augmentation_quasiIso {M : ModuleCat.{u} R}
    (P : ProjectiveResolution M) (G : ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ q, Module.Flat R (G.X q)] :
    QuasiIso (mapBifunctorMap P.π (𝟙 G)
      (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)) :=
  flatComplexTensor_quasiIso P.π G

/-- In a tensor total of two resolutions the first literal augmentation is a
quasi-isomorphism, with no flatness assumption on either resolved module. -/
theorem tensorProjectiveResolutions_augmentation_quasiIso
    {M N : ModuleCat.{u} R} (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    QuasiIso (mapBifunctorMap P.π (𝟙 Q.complex)
      (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)) :=
  flatComplexTensor_augmentation_quasiIso P Q.complex

/-- The double-resolution tensor total computes actual one-sided Tor in every degree. -/
noncomputable def tensorProjectiveResolutionsTorIso
    {M N : ModuleCat.{u} R} (P : ProjectiveResolution M) (Q : ProjectiveResolution N) (n : ℕ) :
    (mapBifunctor P.complex Q.complex
        (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)).homology n ≅
      (((Tor (ModuleCat R) n).obj M).obj N) := by
  letI := tensorProjectiveResolutions_augmentation_quasiIso P Q
  exact isoOfQuasiIsoAt (mapBifunctorMap P.π (𝟙 Q.complex)
      (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)) n ≪≫
    flatComplexTensorSingleTorIso M Q n

/-- The Tor comparison is induced by the actual first-resolution augmentation. -/
@[simp]
theorem tensorProjectiveResolutionsTorIso_hom
    {M N : ModuleCat.{u} R} (P : ProjectiveResolution M) (Q : ProjectiveResolution N) (n : ℕ) :
    (tensorProjectiveResolutionsTorIso P Q n).hom =
      homologyMap (mapBifunctorMap P.π (𝟙 Q.complex)
        (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)) n ≫
          (flatComplexTensorSingleTorIso M Q n).hom := rfl

end ModuleCat.TorComparison
