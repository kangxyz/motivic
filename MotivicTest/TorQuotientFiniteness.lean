/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FiniteGeneration
public import Motivic.Aglib.Algebra.Homology.Koszul.FiniteTor
public import Motivic.Aglib.Algebra.Homology.Koszul.ScalarRestriction.Basic
public import Mathlib.RingTheory.KrullDimension.PID

/-! # Actual finite quotient-supported Tor, including nonzero higher Tor -/

@[expose] public section

noncomputable section

open CategoryTheory
open HomologicalComplex
open _root_.ComplexShape
open _root_.HomologicalComplex
open _root_.HomologicalComplex₂
open _root_.ModuleCat.TorComparison
open _root_.ChainComplex.Koszul

namespace Motivic.MotivicTest.TorQuotientFiniteness

/-- Arbitrary finite modules need no chosen finite resolution as an input. -/
theorem arbitraryFiniteModules (R : Type) [CommRing R] [IsNoetherianRing R]
    (M N : ModuleCat R) [Module.Finite R M] [Module.Finite R N] (n : ℕ) :
    Module.Finite R (((Tor (ModuleCat R) n).obj M).obj N) := inferInstance

/-- Arbitrary actual support ideals give finite modules over their full sum quotient. -/
theorem arbitrarySupportQuotients (R : Type) [CommRing R] [IsNoetherianRing R]
    (J K : Ideal R) (n : ℕ) :
    Module.Finite (R ⧸ (J ⊔ K)) (torSupportModule J K n) := inferInstance

/-- The support ideal in the concrete test retains the nilpotent class of two. -/
abbrev fourIdeal : Ideal ℤ := Ideal.ofList [4]

/-- The actual test ideal is not radical. -/
theorem fourIdeal_not_radical : ¬ fourIdeal.IsRadical := by
  intro h
  have ht : (2 : ℤ) ∈ fourIdeal :=
    (Ideal.isRadical_iff_pow_one_lt (I := fourIdeal) 2 (by decide)).mp h 2 (by
      norm_num [fourIdeal, Ideal.ofList_singleton, Ideal.mem_span_singleton])
  norm_num [fourIdeal, Ideal.ofList_singleton, Ideal.mem_span_singleton] at ht

/-- The coefficient ring is the literal nonradical quotient. -/
abbrev Q := ℤ ⧸ fourIdeal

instance : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr (by
  intro h
  have : (1 : ℤ) ∈ fourIdeal := h ▸ (show (1 : ℤ) ∈ (⊤ : Ideal ℤ) from trivial)
  norm_num [fourIdeal, Ideal.ofList_singleton, Ideal.mem_span_singleton] at this)

/-- The test's regular ambient equation acts by zero on its coefficient module. -/
theorem four_image_zero : Ideal.Quotient.mk fourIdeal (4 : ℤ) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simp [fourIdeal]

/-- The integer equation remains regular on the ambient ring. -/
theorem four_regular : RingTheory.Sequence.IsWeaklyRegular ℤ [(4 : ℤ)] := by
  rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  intro x y h
  change (4 : ℤ) * x = 4 * y at h
  exact mul_left_cancel₀ (by decide : (4 : ℤ) ≠ 0) h

/-- The zero equation has actual degree-one homology equal to its ring coefficients. -/
def zeroHomologyOneIso (A : Type) [CommRing A] :
    (coefficientComplex (ModuleCat.of A A) [0]).homology 1 ≅ ModuleCat.of A A :=
  (homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) 1).mapIso
      (eqToIso (coefficientComplex_ring [0]) ≪≫ singletonIso 0) ≪≫
    singleHomologyOneIso A (0 : A) ≪≫
    (show LinearMap.ker (LinearMap.lsmul A A 0) ≃ₗ[A] A from
      { toFun := Subtype.val
        invFun := fun x => ⟨x, by simp⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }).toModuleIso

/-- The actual degree-one Tor of the nonradical quotient with itself is nonzero. -/
def higherTorIso :
    ((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ Q)).obj (ModuleCat.of ℤ Q) ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk fourIdeal)).obj (ModuleCat.of Q Q) := by
  let f := Ideal.Quotient.mk fourIdeal
  let M := ModuleCat.of Q Q
  let e : ModuleCat.of ℤ Q ≅ (ModuleCat.restrictScalars f).obj M :=
    (LinearEquiv.refl ℤ Q).toModuleIso
  exact finiteTorIsoHomology (ModuleCat.of ℤ Q) [4] four_regular 1 ≪≫
    (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 1).mapIso (coefficientIso e [4]) ≪≫
    coefficientRestrictHomologyIso f M [4] 1 ≪≫
    (ModuleCat.restrictScalars f).mapIso
      ((homologyFunctor (ModuleCat Q) (ComplexShape.down ℕ) 1).mapIso
        (eqToIso (by
          change coefficientComplex (ModuleCat.of Q Q) [Ideal.Quotient.mk fourIdeal 4] = _
          rw [four_image_zero])) ≪≫
        zeroHomologyOneIso Q)

/-- The higher-Tor consumer really has positive-degree classes. -/
theorem higherTor_nonzero :
    ¬ Limits.IsZero (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ Q)).obj
      (ModuleCat.of ℤ Q)) := by
  intro h
  have : Subsingleton Q := ModuleCat.isZero_iff_subsingleton.mp
    (h.of_iso higherTorIso.symm)
  exact zero_ne_one (Subsingleton.elim (0 : Q) 1)

/-- This same nonzero degree-one module is finite with its literal quotient-support action. -/
theorem higherTor_finite_support :
    Module.Finite (ℤ ⧸ (fourIdeal ⊔ fourIdeal)) (torSupportModule fourIdeal fourIdeal 1) :=
  inferInstance

/-- The constructed quotient action recovers the original positive-degree Tor module. -/
def higherTorRestrict :
    ((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ Q)).obj (ModuleCat.of ℤ Q) ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (fourIdeal ⊔ fourIdeal))).obj
        (torSupportModule fourIdeal fourIdeal 1) :=
  torSupportModuleRestrictIso fourIdeal fourIdeal 1

/-- Scalar lifting applies to an actual endomorphism of this nonzero higher Tor. -/
def higherTorDouble : torSupportModule fourIdeal fourIdeal 1 ⟶
    torSupportModule fourIdeal fourIdeal 1 :=
  quotientLinearMap _ (quotient_support_le_annihilator fourIdeal fourIdeal 1)
    (quotient_support_le_annihilator fourIdeal fourIdeal 1) ((2 : ℤ) • 𝟙 _)

/-- The descended endomorphism retains the original ambient multiplication by two. -/
theorem higherTorDouble_apply
    (x : ((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ Q)).obj (ModuleCat.of ℤ Q)) :
    higherTorDouble x = (2 : ℤ) • x := rfl

end Motivic.MotivicTest.TorQuotientFiniteness
