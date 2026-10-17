/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulScalarRestrictionLength
public import Motivic.Algebra.Homology.KoszulSingleTensorElements
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Actual nonflat quotient consumers of Koszul scalar restriction

Arbitrary ideal quotients and arbitrary quotient-ring modules instantiate the
actual chain and homology comparisons. The map from the integers to Z/2 is
proved nonflat, yet its comparison still exists; the degree-one differential
on the generator for the scalar 2 is proved zero. Surjective quotient lengths
and finite Euler sums consume the same constructed comparisons.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Motivic.Koszul Motivic.LengthEuler

namespace MotivicTest.KoszulScalarRestriction

/-- Arbitrary quotient maps and arbitrary modules admit the actual projection isomorphism. -/
def quotientComparison (R : Type u) [CommRing R] (I : Ideal R)
    (M : ModuleCat.{u} (R ⧸ I)) (s : List R) :
    coefficientComplex ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M) s ≅
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (coefficientComplex M (s.map (Ideal.Quotient.mk I))) :=
  coefficientRestrictIso (Ideal.Quotient.mk I) M s

/-- The arbitrary quotient comparison is an actual isomorphism on homology as well. -/
def quotientHomology (R : Type u) [CommRing R] (I : Ideal R)
    (M : ModuleCat.{u} (R ⧸ I)) (s : List R) (n : ℕ) :
    (coefficientComplex ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M) s).homology n ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
        ((coefficientComplex M (s.map (Ideal.Quotient.mk I))).homology n) :=
  coefficientRestrictHomologyIso (Ideal.Quotient.mk I) M s n

/-- The literal quotient comparison preserves old-column generators. -/
theorem quotientOldColumn (R : Type u) [CommRing R] (I : Ideal R) (a : R)
    (K : ChainComplex (ModuleCat.{u} (R ⧸ I)) ℕ) (n : ℕ)
    (x : (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (K.X n)) :
    (singleTensorRestrictIso (Ideal.Quotient.mk I) a K).hom.f n
      (singleTensorιZero a (crossMappedComplex (ModuleCat.restrictScalars (Ideal.Quotient.mk I)) K)
        n x) = singleTensorιZero (Ideal.Quotient.mk I a) K n (x : K.X n) :=
  singleTensorRestrictIso_hom_ιZero (Ideal.Quotient.mk I) a K n x

/-- Quotient-ring coefficients need not be flat over the integers. -/
theorem modTwo_not_flat : ¬ Module.Flat ℤ (ZMod 2) := by
  intro h
  let := h
  have hz : (2 : ℤ) • (1 : ZMod 2) = 0 := by decide
  have hone : (1 : ZMod 2) = 0 := (smul_eq_zero_iff_right (by decide : (2 : ℤ) ≠ 0)).mp hz
  exact one_ne_zero hone

/-- The actual integer-to-Z/2 ring map is not flat. -/
theorem modTwo_map_not_flat : ¬ (Int.castRingHom (ZMod 2)).Flat := by
  change ¬ (algebraMap ℤ (ZMod 2)).Flat
  rw [RingHom.flat_algebraMap_iff]
  exact modTwo_not_flat

/-- Even the nonflat integer-to-Z/2 map has the actual listwise Koszul comparison. -/
def modTwoComparison (M : ModuleCat (ZMod 2)) (s : List ℤ) :
    coefficientComplex ((ModuleCat.restrictScalars (Int.castRingHom (ZMod 2))).obj M) s ≅
      ((ModuleCat.restrictScalars (Int.castRingHom (ZMod 2))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (coefficientComplex M (s.map (Int.castRingHom (ZMod 2)))) :=
  coefficientRestrictIso (Int.castRingHom (ZMod 2)) M s

set_option backward.isDefEq.respectTransparency false in
/-- The actual scalar-2 differential is zero on the shifted degree-one generators. -/
theorem modTwo_d_generator (M : ModuleCat (ZMod 2)) (x : M) :
    (coefficientComplex ((ModuleCat.restrictScalars (Int.castRingHom (ZMod 2))).obj M) [2]).d 1 0
      (singleTensorιOne (2 : ℤ)
        (coefficientComplex ((ModuleCat.restrictScalars (Int.castRingHom (ZMod 2))).obj M) [])
        0 x) = 0 := by
  change (HomologicalComplex.tensorObj (singleComplex ℤ 2)
    (coefficientComplex ((ModuleCat.restrictScalars (Int.castRingHom (ZMod 2))).obj M) [])).d 1 0
    (singleTensorιOne (2 : ℤ) _ 0 x) = 0
  erw [singleTensor_d_ιOne_zero_apply]
  change singleTensorιZero (2 : ℤ)
    (coefficientComplex ((ModuleCat.restrictScalars (Int.castRingHom (ZMod 2))).obj M) []) 0
    ((Int.castRingHom (ZMod 2)) (2 : ℤ) • x) = 0
  rw [show (Int.castRingHom (ZMod 2)) (2 : ℤ) = 0 by decide, zero_smul]
  exact map_zero _

/-- An arbitrary quotient map preserves actual all-degree homology lengths. -/
theorem quotientLength (R : Type u) [CommRing R] (I : Ideal R)
    (M : ModuleCat.{u} (R ⧸ I)) (s : List R) (n : ℕ) :
    Module.length R
      ((coefficientComplex
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M) s).homology n) =
      Module.length (R ⧸ I)
        ((coefficientComplex M (s.map (Ideal.Quotient.mk I))).homology n) :=
  coefficientRestrict_length (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective M s n

/-- Nonreduced base rings are admitted by the length comparison. -/
theorem nonreducedQuotientLength (I : Ideal (ZMod 4)) (M : ModuleCat (ZMod 4 ⧸ I))
    (s : List (ZMod 4)) (n : ℕ) :
    Module.length (ZMod 4)
      ((coefficientComplex
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M) s).homology n) =
      Module.length (ZMod 4 ⧸ I)
        ((coefficientComplex M (s.map (Ideal.Quotient.mk I))).homology n) :=
  quotientLength (ZMod 4) I M s n

/-- Quotient projection preserves genuine finite alternating Euler sums. -/
theorem quotientEuler (R : Type u) [CommRing R] (I : Ideal R)
    (M : ModuleCat.{u} (R ⧸ I)) (s : List R)
    (h : FiniteLengthSupport (fun n ↦
      (coefficientComplex
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M) s).homology n)) :
    signedLengthSum (fun n ↦
      (coefficientComplex ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M) s).homology n)
      (fun n ↦ (-1 : ℤ) ^ n) h =
    signedLengthSum (fun n ↦ (coefficientComplex M (s.map (Ideal.Quotient.mk I))).homology n)
      (fun n ↦ (-1 : ℤ) ^ n)
      ((coefficientRestrict_finiteLengthSupport_iff (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective M s).mp h) :=
  coefficientRestrict_signedLengthSum (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective M s _ h

end MotivicTest.KoszulScalarRestriction
