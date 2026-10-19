/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.FiniteProjection.Extension
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Arbitrary-complex Koszul extension and localization consumers

The chain comparison is exercised over the genuinely nonflat integer quotient
Z/4, on arbitrary complexes and repeated/zero equations. Actual homology is
compared only for explicitly flat maps, including localization at a prime.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory _root_.ChainComplex.Koszul

namespace MotivicTest.KoszulFiniteProjectionExtension

/-- Scalar extension in the first chain consumer is genuinely nonflat. -/
theorem modFourNotFlat : ¬ Module.Flat ℤ (ZMod 4) := by
  intro h
  let := h
  have hz : (4 : ℤ) • (1 : ZMod 4) = 0 := by decide
  have hone : (1 : ZMod 4) = 0 :=
    (smul_eq_zero_iff_right (by decide : (4 : ℤ) ≠ 0)).mp hz
  exact (by decide : (1 : ZMod 4) ≠ 0) hone

/-- Nonflat extension still commutes at chain level with every finite Koszul list. -/
def nonflatComplexIso (K : ChainComplex (ModuleCat ℤ) ℕ) (s : List ℤ) :
    crossMappedComplex (ModuleCat.extendScalars (Int.castRingHom (ZMod 4)))
        (HomologicalComplex.tensorObj (chainComplex s) K) ≅
      HomologicalComplex.tensorObj
        (chainComplex (s.map (Int.castRingHom (ZMod 4))))
        (crossMappedComplex (ModuleCat.extendScalars (Int.castRingHom (ZMod 4))) K) :=
  koszulTensorExtendIso (Int.castRingHom (ZMod 4)) s K

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The empty-list extension comparison uses actual tensor-unit isomorphisms. -/
def emptyListIso (f : R →+* S) (K : ChainComplex (ModuleCat R) ℕ) :
    crossMappedComplex (ModuleCat.extendScalars f)
        (HomologicalComplex.tensorObj (chainComplex ([] : List R)) K) ≅
      HomologicalComplex.tensorObj (chainComplex ([] : List S))
        (crossMappedComplex (ModuleCat.extendScalars f) K) :=
  koszulTensorExtendIso f [] K

/-- Every scalar, including a repeated or zero equation, uses its literal image. -/
theorem actualScalarMap (f : R →+* S) (a : R) (M : ModuleCat R) :
    (ModuleCat.extendScalars f).map (ModuleCat.ofHom (LinearMap.lsmul R M a)) =
      ModuleCat.ofHom (LinearMap.lsmul S ((ModuleCat.extendScalars f).obj M) (f a)) :=
  extendScalars_map_lsmul f a M

/-- The repeated/zero list has its actual component differential square. -/
theorem repeatedZeroDifferential (f : R →+* S) (a : R)
    (K : ChainComplex (ModuleCat R) ℕ) (i j : ℕ) :
    (koszulTensorExtendIso f [a, a, 0] K).hom.f i ≫
        (HomologicalComplex.tensorObj (chainComplex ([a, a, 0].map f))
          (crossMappedComplex (ModuleCat.extendScalars f) K)).d i j =
      (ModuleCat.extendScalars f).map
          ((HomologicalComplex.tensorObj (chainComplex [a, a, 0]) K).d i j) ≫
        (koszulTensorExtendIso f [a, a, 0] K).hom.f j :=
  koszulTensorExtendIso_hom_comm f [a, a, 0] K i j

/-- Naturality holds for actual unrestricted chain maps. -/
theorem actualChainMapNaturality (f : R →+* S) (s : List R)
    {K L : ChainComplex (ModuleCat R) ℕ} (g : K ⟶ L) :
    (extendChainFunctor f).map ((koszulTensorFunctor s).map g) ≫
        (koszulTensorExtendIso f s L).hom =
      (koszulTensorExtendIso f s K).hom ≫
        (koszulTensorFunctor (s.map f)).map ((extendChainFunctor f).map g) :=
  koszulTensorExtendIso_naturality f s g

/-- Homology commutation explicitly receives the genuine flatness premise. -/
def actualFlatHomologyIso (f : R →+* S) (hf : f.Flat) (s : List R)
    (K : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    (ModuleCat.extendScalars f).obj
        ((HomologicalComplex.tensorObj (chainComplex s) K).homology n) ≅
      (HomologicalComplex.tensorObj (chainComplex (s.map f))
        (crossMappedComplex (ModuleCat.extendScalars f) K)).homology n :=
  flatKoszulTensorExtendHomologyIso f hf s K n

/-- Localization at a prime supplies flatness; the complex has no boundedness
or finite-homology premise, and the list may contain repeated zero divisors. -/
def atPrimeHomologyIso (p : Ideal R) [p.IsPrime] (a : R)
    (K : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    (ModuleCat.extendScalars (algebraMap R (Localization.AtPrime p))).obj
        ((HomologicalComplex.tensorObj (chainComplex [0, a, a]) K).homology n) ≅
      (HomologicalComplex.tensorObj
        (chainComplex ([0, a, a].map (algebraMap R (Localization.AtPrime p))))
        (crossMappedComplex
          (ModuleCat.extendScalars (algebraMap R (Localization.AtPrime p))) K)).homology n :=
  localizationKoszulTensorHomologyIso p.primeCompl [0, a, a] K n

end MotivicTest.KoszulFiniteProjectionExtension
