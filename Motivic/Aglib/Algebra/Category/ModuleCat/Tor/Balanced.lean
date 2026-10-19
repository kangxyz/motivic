/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatComplexTensorQuasiIso
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Motivic.Aglib.Algebra.Homology.TotalComplex.NatShapeSymmetry

/-!
# Genuine balanced Tor from two projective resolutions

Both actual one-sided Tor computations are compared to the signed tensor
of two genuine resolutions. Componentwise module braiding and the signed
bicomplex flip identify the two totals. This constructs an all-degree
isomorphism of modules, without assuming balanced derived functors or
flatness of either resolved module. Naturality of the final Tor isomorphism
is a separate statement and is not asserted here.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex

universe u

section
open _root_.ModuleCat.TorComparison


variable {R : Type u} [CommRing R]

/-- The actual module braiding commutes with both bicomplex differentials. -/
def _root_.ModuleCat.TorComparison.tensorBicomplexBraidingIso (K L : ChainComplex (ModuleCat.{u} R)
    ℕ) :
    (((curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj K).obj L ≅
      ((((curriedTensor (ModuleCat R)).flip).mapBifunctorHomologicalComplex
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj K).obj L :=
  Hom.isoOfComponents
    (fun i ↦ Hom.isoOfComponents
      (fun j ↦ β_ (K.X i) (L.X j)) (by
        intro j j' _
        exact (((BraidedCategory.curriedBraidingNatIso (ModuleCat R)).app
          (K.X i)).hom.naturality (L.d j j')).symm)) (by
      intro i i' _
      ext1 j
      exact congrArg (fun t ↦ t.app (L.X j))
        ((BraidedCategory.curriedBraidingNatIso (ModuleCat R)).hom.naturality
          (K.d i i')).symm)

/-- The literal signed total tensor complexes are symmetric, including the
Koszul sign supplied by the actual total-complex flip. -/
def _root_.ModuleCat.TorComparison.tensorTotalSymmetryIso (K L : ChainComplex (ModuleCat.{u} R) ℕ) :
    mapBifunctor K L (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) ≅
      mapBifunctor L K (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) :=
  HomologicalComplex₂.total.mapIso (tensorBicomplexBraidingIso K L) (ComplexShape.down ℕ) ≪≫
    mapBifunctorFlipIso L K (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)

/-- Two genuine projective resolutions construct balanced categorical Tor. -/
def _root_.ModuleCat.TorComparison.torBalanceIsoOfResolutions {M N : ModuleCat.{u} R}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) (n : ℕ) :
    ((Tor (ModuleCat R) n).obj M).obj N ≅ ((Tor (ModuleCat R) n).obj N).obj M :=
  (tensorProjectiveResolutionsTorIso P Q n).symm ≪≫
    (homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
      (tensorTotalSymmetryIso P.complex Q.complex) ≪≫
    tensorProjectiveResolutionsTorIso Q P n

/-- Actual Tor of arbitrary modules over a commutative ring is balanced in
all natural degrees, as an isomorphism in the original module category. -/
def _root_.ModuleCat.TorComparison.torBalanceIso (M N : ModuleCat.{u} R) (n : ℕ) :
    ((Tor (ModuleCat R) n).obj M).obj N ≅ ((Tor (ModuleCat R) n).obj N).obj M :=
  torBalanceIsoOfResolutions (projectiveResolution M) (projectiveResolution N) n

end
