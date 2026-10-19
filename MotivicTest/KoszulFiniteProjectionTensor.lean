/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.FiniteProjection.Tensor
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Arbitrary-complex nonflat Koszul projection consumers

The finite-list tensor comparison is instantiated on unrestricted complexes
over the nonflat nonreduced integer quotient Z/4 and along the nonsurjective
integer-to-rational map. Repeated and zero equations exercise literal
component differential and naturality squares; an empty list exercises units.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory _root_.ChainComplex.Koszul

namespace MotivicTest.KoszulFiniteProjectionTensor

/-- The nonreduced target ring in the concrete restriction test is not flat. -/
theorem modFourNotFlat : ¬ Module.Flat ℤ (ZMod 4) := by
  intro h
  let := h
  have hz : (4 : ℤ) • (1 : ZMod 4) = 0 := by decide
  have hone : (1 : ZMod 4) = 0 :=
    (smul_eq_zero_iff_right (by decide : (4 : ℤ) ≠ 0)).mp hz
  exact (by decide : (1 : ZMod 4) ≠ 0) hone

/-- Arbitrary complexes over this nonflat target admit the actual finite-list
comparison; they need not be coefficient complexes or have finite homology. -/
def nonflatComplexIso (K : ChainComplex (ModuleCat (ZMod 4)) ℕ) (s : List ℤ) :
    crossMappedComplex (ModuleCat.restrictScalars (Int.castRingHom (ZMod 4)))
        (HomologicalComplex.tensorObj
          (chainComplex (s.map (Int.castRingHom (ZMod 4)))) K) ≅
      HomologicalComplex.tensorObj (chainComplex s)
        (crossMappedComplex (ModuleCat.restrictScalars (Int.castRingHom (ZMod 4))) K) :=
  koszulTensorRestrictIso (Int.castRingHom (ZMod 4)) s K

/-- The second concrete ring map is genuinely nonsurjective. -/
theorem integersToRationalsNotSurjective : ¬ Function.Surjective (Int.castRingHom ℚ) := by
  intro h
  obtain ⟨n, hn⟩ := h (1 / 2)
  have he : (n : ℚ) = 1 / 2 := hn
  have htwo : (2 : ℚ) * (n : ℚ) = 1 := by rw [he]; norm_num
  have hInt : (2 : ℤ) * n = 1 := by exact_mod_cast htwo
  omega

/-- Arbitrary rational complexes admit the restriction comparison without
surjectivity, finite coefficients, or boundedness assumptions. -/
def nonsurjectiveComplexIso (K : ChainComplex (ModuleCat ℚ) ℕ) (s : List ℤ) :
    crossMappedComplex (ModuleCat.restrictScalars (Int.castRingHom ℚ))
        (HomologicalComplex.tensorObj (chainComplex (s.map (Int.castRingHom ℚ))) K) ≅
      HomologicalComplex.tensorObj (chainComplex s)
        (crossMappedComplex (ModuleCat.restrictScalars (Int.castRingHom ℚ)) K) :=
  koszulTensorRestrictIso (Int.castRingHom ℚ) s K

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The empty list comparison uses the actual tensor-unit comparisons. -/
def emptyListIso (f : R →+* S) (K : ChainComplex (ModuleCat S) ℕ) :
    crossMappedComplex (ModuleCat.restrictScalars f)
        (HomologicalComplex.tensorObj (chainComplex ([] : List S)) K) ≅
      HomologicalComplex.tensorObj (chainComplex ([] : List R))
        (crossMappedComplex (ModuleCat.restrictScalars f) K) :=
  koszulTensorRestrictIso f [] K

/-- A repeated/zero list respects actual differentials on an arbitrary complex. -/
theorem repeatedZeroDifferential (f : R →+* S) (a : R)
    (K : ChainComplex (ModuleCat S) ℕ) (i j : ℕ) :
    (koszulTensorRestrictIso f [a, a, 0] K).hom.f i ≫
        (HomologicalComplex.tensorObj (chainComplex [a, a, 0])
          (crossMappedComplex (ModuleCat.restrictScalars f) K)).d i j =
      (ModuleCat.restrictScalars f).map
          ((HomologicalComplex.tensorObj (chainComplex ([a, a, 0].map f)) K).d i j) ≫
        (koszulTensorRestrictIso f [a, a, 0] K).hom.f j :=
  koszulTensorRestrictIso_hom_comm f [a, a, 0] K i j

/-- Naturality holds for unrestricted chain maps, not only module coefficients. -/
theorem actualChainMapNaturality (f : R →+* S) (s : List R)
    {K L : ChainComplex (ModuleCat S) ℕ} (g : K ⟶ L) :
    (restrictChainFunctor f).map ((koszulTensorFunctor (s.map f)).map g) ≫
        (koszulTensorRestrictIso f s L).hom =
      (koszulTensorRestrictIso f s K).hom ≫
        (koszulTensorFunctor s).map ((restrictChainFunctor f).map g) :=
  koszulTensorRestrictIso_naturality f s g

/-- Homology restriction also applies to every degree of an arbitrary complex. -/
def actualHomologyIso (f : R →+* S) (s : List R)
    (K : ChainComplex (ModuleCat S) ℕ) (n : ℕ) :
    (HomologicalComplex.tensorObj (chainComplex s)
        (crossMappedComplex (ModuleCat.restrictScalars f) K)).homology n ≅
      (ModuleCat.restrictScalars f).obj
        ((HomologicalComplex.tensorObj (chainComplex (s.map f)) K).homology n) :=
  koszulTensorRestrictHomologyIso f s K n

end MotivicTest.KoszulFiniteProjectionTensor
