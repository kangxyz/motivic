/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Bifunctor.TotalCofiber
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-! Module and literal-resolution consumers of the signed tensor-total cofiber isomorphism. -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex

universe u

namespace Motivic.MotivicTest.TorComparisonTensorTotalCofiber

variable {R : Type u} [CommRing R]
  {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)
  (G : ChainComplex (ModuleCat.{u} R) ℕ)

/-- Every actual module chain map has the stated cofiber-total isomorphism. -/
noncomputable def arbitraryModuleMap :
    homotopyCofiber (mapBifunctorMap f (𝟙 G)
      (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)) ≅
    mapBifunctor (homotopyCofiber f) G
      (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) :=
  tensorTotalCofiberIso (curriedTensor (ModuleCat R)) f G

/-- The construction applies to the literal augmentation of an arbitrary resolution. -/
noncomputable def literalResolutionAugmentation {M : ModuleCat.{u} R}
    (P : ProjectiveResolution M) :
    homotopyCofiber (mapBifunctorMap P.π (𝟙 G)
      (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)) ≅
    mapBifunctor (homotopyCofiber P.π) G
      (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) :=
  tensorTotalCofiberIso (curriedTensor (ModuleCat R)) P.π G

/-- The forward isomorphism is the actual canonical cofiber-desc map. -/
theorem literalForwardMap :
    (arbitraryModuleMap f G).hom =
      tensorTotalCofiberMap (curriedTensor (ModuleCat R)) f G :=
  tensorTotalCofiberIso_hom (curriedTensor (ModuleCat R)) f G

/-- The isomorphism intertwines the signed differential in every degree. -/
theorem signedDifferential (i j : ℕ) :
    (arbitraryModuleMap f G).hom.f i ≫
        (mapBifunctor (homotopyCofiber f) G
          (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)).d i j =
    (homotopyCofiber (mapBifunctorMap f (𝟙 G)
      (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ))).d i j ≫
        (arbitraryModuleMap f G).hom.f j :=
  (arbitraryModuleMap f G).hom.comm i j

end Motivic.MotivicTest.TorComparisonTensorTotalCofiber
