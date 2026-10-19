/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.AmbientLength
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.AmbientMiddle
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of genuine ambient Tor length and Euler comparison -/

@[expose] public section

open CategoryTheory
open _root_.ComplexShape
open _root_.HomologicalComplex
open _root_.HomologicalComplex₂
open _root_.ModuleCat
open _root_.ModuleCat.TorComparison
open _root_.HomologicalComplex.ModuleLengthEuler
open scoped TensorProduct Algebra.TensorProduct.MiddleDiagonal

universe u

namespace MotivicTest.TorComparisonAmbientLength

/-- Restricting an arbitrary quotient module preserves its actual length. -/
theorem quotientRestriction (R : Type u) [CommRing R] (I : Ideal R)
    (M : ModuleCat.{u} (R ⧸ I)) :
    Module.length R ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M) =
      Module.length (R ⧸ I) M :=
  length_restrictScalars_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective M

/-- The scalar-length theorem does not require a reduced base. -/
theorem nonreducedRestriction (I : Ideal (ZMod 4)) (M : ModuleCat.{0} (ZMod 4 ⧸ I)) :
    Module.length (ZMod 4) ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M) =
      Module.length (ZMod 4 ⧸ I) M :=
  quotientRestriction (ZMod 4) I M

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  (M : ModuleCat.{u} (A ⊗[k] B)) (N : ModuleCat.{u} (B ⊗[k] C))

/-- The actual middle diagonal discharges surjectivity and both factor-flatness hypotheses. -/
theorem middleLength (n : ℕ) :
    Module.length (_root_.Algebra.TensorProduct.MiddleDiagonal.ambientRing k A B C)
      (ambientTorFamily (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B C).toRingHom
          M N n) =
    Module.length (_root_.Algebra.TensorProduct.MiddleDiagonal.tripleRing k A B C)
      (extendedTorFamily (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B C).toRingHom
          M N n) := by
  apply ambientTor_length _ (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap_surjective k A
      B C)
  · rw [ambientMiddle_leftMap]
    exact _root_.AlgebraicGeometry.Scheme.Products.MiddleDiagonal.leftMap_flat k A B C
  · rw [ambientMiddle_rightMap]
    exact _root_.AlgebraicGeometry.Scheme.Products.MiddleDiagonal.rightMap_flat k A B C

/-- The middle-diagonal theorem applies to arbitrary quotient supports. -/
theorem quotientSupportLength (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (n : ℕ) :
    Module.length (_root_.Algebra.TensorProduct.MiddleDiagonal.ambientRing k A B C)
      (ambientTorFamily (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B C).toRingHom
        (ModuleCat.of (A ⊗[k] B) ((A ⊗[k] B) ⧸ I))
        (ModuleCat.of (B ⊗[k] C) ((B ⊗[k] C) ⧸ J)) n) =
    Module.length (_root_.Algebra.TensorProduct.MiddleDiagonal.tripleRing k A B C)
      (extendedTorFamily (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B C).toRingHom
        (ModuleCat.of (A ⊗[k] B) ((A ⊗[k] B) ⧸ I))
        (ModuleCat.of (B ⊗[k] C) ((B ⊗[k] C) ⧸ J)) n) :=
  middleLength k A B C _ _ n

/-- Actual finite degree support transfers in both directions at the middle diagonal. -/
theorem middleFiniteSupport :
    FiniteLengthSupport (ambientTorFamily (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k
        A B C).toRingHom M N) ↔
      FiniteLengthSupport
        (extendedTorFamily (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B
            C).toRingHom M N) := by
  apply ambientTor_finiteLengthSupport_iff _
      (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap_surjective k A B C)
  · rw [ambientMiddle_leftMap]
    exact _root_.AlgebraicGeometry.Scheme.Products.MiddleDiagonal.leftMap_flat k A B C
  · rw [ambientMiddle_rightMap]
    exact _root_.AlgebraicGeometry.Scheme.Products.MiddleDiagonal.rightMap_flat k A B C

/-- The genuine alternating sum transfers without converting infinite lengths to integers. -/
theorem middleEuler
    (h : FiniteLengthSupport
      (ambientTorFamily (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B C).toRingHom
          M N)) :
    signedLengthSum (ambientTorFamily (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B
        C).toRingHom M N)
      (fun n ↦ (-1 : ℤ) ^ n) h =
      signedLengthSum (extendedTorFamily (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k
          A B C).toRingHom M N)
        (fun n ↦ (-1 : ℤ) ^ n) ((middleFiniteSupport k A B C M N).mp h) := by
  apply ambientTor_signedLengthSum _
      (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap_surjective k A B C)
  · rw [ambientMiddle_leftMap]
    exact _root_.AlgebraicGeometry.Scheme.Products.MiddleDiagonal.leftMap_flat k A B C
  · rw [ambientMiddle_rightMap]
    exact _root_.AlgebraicGeometry.Scheme.Products.MiddleDiagonal.rightMap_flat k A B C

end MotivicTest.TorComparisonAmbientLength
