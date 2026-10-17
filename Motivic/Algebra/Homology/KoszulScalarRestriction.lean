/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulScalarRestrictionTensor
public import Motivic.Algebra.Homology.KoszulCoefficientComplex
public import Motivic.Algebra.Homology.TorComparison.AmbientScalar
public import Mathlib.Algebra.Homology.Additive

/-!
# Nonflat scalar restriction for actual finite Koszul complexes

For every commutative-ring map, the actual Koszul complex on a finite list
with restricted module coefficients is isomorphic to the restriction of the
Koszul complex on the image list. The explicit two-column isomorphism preserves
both columns and their scalar differentials. No flatness assumption on the
ring map or the coefficient module occurs. Exact restriction also gives the
actual homology comparison, with its literal source-ring action.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace Motivic.Koszul

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Restriction carries target scalar multiplication to the literal source action. -/
theorem restrictScalars_map_lsmul (f : R →+* S) (a : R) (M : ModuleCat.{u} S) :
    (ModuleCat.restrictScalars f).map (ModuleCat.ofHom (LinearMap.lsmul S M (f a))) =
      ModuleCat.ofHom (LinearMap.lsmul R ((ModuleCat.restrictScalars f).obj M) a) := rfl

/-- The restricted scalar action is multiplication by the image of the scalar. -/
theorem restrictScalars_smul (f : R →+* S) (a : R) (M : ModuleCat.{u} S)
    (x : (ModuleCat.restrictScalars f).obj M) : a • x = f a • (x : M) := rfl

/-- The explicit nonflat one-element projection comparison. -/
def singleTensorRestrictIso (f : R →+* S) (a : R)
    (K : ChainComplex (ModuleCat.{u} S) ℕ) :
    HomologicalComplex.tensorObj (singleComplex R a)
        (crossMappedComplex (ModuleCat.restrictScalars f) K) ≅
      crossMappedComplex (ModuleCat.restrictScalars f)
        (HomologicalComplex.tensorObj (singleComplex S (f a)) K) :=
  (singleTensorCrossMapIso (ModuleCat.restrictScalars f) (f a) a K
    (restrictScalars_map_lsmul f a)).symm

/-- On the old-column generators the comparison is the underlying identity. -/
theorem singleTensorRestrictIso_hom_ιZero (f : R →+* S) (a : R)
    (K : ChainComplex (ModuleCat.{u} S) ℕ) (n : ℕ)
    (x : (ModuleCat.restrictScalars f).obj (K.X n)) :
    (singleTensorRestrictIso f a K).hom.f n
        (singleTensorιZero a (crossMappedComplex (ModuleCat.restrictScalars f) K) n x) =
      singleTensorιZero (f a) K n (x : K.X n) :=
  ConcreteCategory.congr_hom
    (ιZero_singleTensorCrossMapFromX (ModuleCat.restrictScalars f) (f a) a K n) x

/-- On the shifted-column generators the comparison is the underlying identity. -/
theorem singleTensorRestrictIso_hom_ιOne (f : R →+* S) (a : R)
    (K : ChainComplex (ModuleCat.{u} S) ℕ) (n : ℕ)
    (x : (ModuleCat.restrictScalars f).obj (K.X n)) :
    (singleTensorRestrictIso f a K).hom.f (n + 1)
        (singleTensorιOne a (crossMappedComplex (ModuleCat.restrictScalars f) K) n x) =
      singleTensorιOne (f a) K n (x : K.X n) :=
  ConcreteCategory.congr_hom
    (ιOne_singleTensorCrossMapFromX (ModuleCat.restrictScalars f) (f a) a K n) x

/-- Recursive scalar restriction, oriented from the mapped target-ring complex. -/
def restrictedCoefficientIso (f : R →+* S) (M : ModuleCat.{u} S) :
    (s : List R) →
      crossMappedComplex (ModuleCat.restrictScalars f) (coefficientComplex M (s.map f)) ≅
        coefficientComplex ((ModuleCat.restrictScalars f).obj M) s
  | [] => (HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars f)
      (ComplexShape.down ℕ) 0).app M
  | a :: s => (singleTensorRestrictIso f a (coefficientComplex M (s.map f))).symm ≪≫
      whiskerLeftIso (singleComplex R a) (restrictedCoefficientIso f M s)

/-- The genuine finite Koszul projection comparison for an arbitrary ring map. -/
def coefficientRestrictIso (f : R →+* S) (M : ModuleCat.{u} S) (s : List R) :
    coefficientComplex ((ModuleCat.restrictScalars f).obj M) s ≅
      ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (coefficientComplex M (s.map f)) :=
  (restrictedCoefficientIso f M s).symm

/-- Exact scalar restriction identifies actual Koszul homology without flatness. -/
def coefficientRestrictHomologyIso (f : R →+* S) (M : ModuleCat.{u} S)
    (s : List R) (n : ℕ) :
    (coefficientComplex ((ModuleCat.restrictScalars f).obj M) s).homology n ≅
      (ModuleCat.restrictScalars f).obj ((coefficientComplex M (s.map f)).homology n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
      (coefficientRestrictIso f M s) ≪≫
    Motivic.TorComparison.ambientRestrictHomologyIso f (coefficientComplex M (s.map f)) n

end Motivic.Koszul
