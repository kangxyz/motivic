/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.AmbientLocalLength
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.AmbientMiddle
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of actual prime-local ambient Tor length and Euler comparison -/

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

namespace MotivicTest.TorComparisonAmbientLocalLength

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  (P : Ideal (_root_.Algebra.TensorProduct.MiddleDiagonal.ambientRing k A B C)) [P.IsPrime]
  (q : Ideal (_root_.Algebra.TensorProduct.MiddleDiagonal.tripleRing k A B C)) [q.IsPrime]
  (hPq : P = q.comap (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B C).toRingHom)
  (M : ModuleCat.{u} (A ⊗[k] B)) (N : ModuleCat.{u} (B ⊗[k] C))

include hPq

/-- The actual middle diagonal discharges surjectivity and both factor-flatness hypotheses. -/
theorem middleLength (n : ℕ) :
    Module.length (Localization.AtPrime P)
      (localizedAmbientTorFamily (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B
          C).toRingHom P M N n) =
    Module.length (Localization.AtPrime q)
      (localizedExtendedTorFamily (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B
          C).toRingHom q M N n) := by
  apply ambientLocalTor_length _ (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap_surjective
      k A B C)
      (hPq := hPq)
  · rw [ambientMiddle_leftMap]
    exact _root_.AlgebraicGeometry.Scheme.Products.MiddleDiagonal.leftMap_flat k A B C
  · rw [ambientMiddle_rightMap]
    exact _root_.AlgebraicGeometry.Scheme.Products.MiddleDiagonal.rightMap_flat k A B C

/-- The middle-diagonal theorem applies to arbitrary quotient supports. -/
theorem quotientSupportLength (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (n : ℕ) :
    Module.length (Localization.AtPrime P)
      (localizedAmbientTorFamily (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B
          C).toRingHom P
        (ModuleCat.of (A ⊗[k] B) ((A ⊗[k] B) ⧸ I))
        (ModuleCat.of (B ⊗[k] C) ((B ⊗[k] C) ⧸ J)) n) =
    Module.length (Localization.AtPrime q)
      (localizedExtendedTorFamily (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B
          C).toRingHom q
        (ModuleCat.of (A ⊗[k] B) ((A ⊗[k] B) ⧸ I))
        (ModuleCat.of (B ⊗[k] C) ((B ⊗[k] C) ⧸ J)) n) :=
  middleLength k A B C P q hPq _ _ n

/-- Actual finite degree support transfers in both directions at the middle diagonal. -/
theorem middleFiniteSupport :
    FiniteLengthSupport
      (localizedAmbientTorFamily (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B
          C).toRingHom P M N) ↔
      FiniteLengthSupport
        (localizedExtendedTorFamily (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B
            C).toRingHom q M N) := by
  apply ambientLocalTor_finiteLengthSupport_iff _
      (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap_surjective k A B C)
      (hPq := hPq)
  · rw [ambientMiddle_leftMap]
    exact _root_.AlgebraicGeometry.Scheme.Products.MiddleDiagonal.leftMap_flat k A B C
  · rw [ambientMiddle_rightMap]
    exact _root_.AlgebraicGeometry.Scheme.Products.MiddleDiagonal.rightMap_flat k A B C

/-- The genuine alternating sum transfers without converting infinite lengths to integers. -/
theorem middleEuler
    (h : FiniteLengthSupport
      (localizedAmbientTorFamily (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B
          C).toRingHom P M N)) :
    signedLengthSum
      (localizedAmbientTorFamily (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B
          C).toRingHom P M N)
      (fun n ↦ (-1 : ℤ) ^ n) h =
      signedLengthSum
        (localizedExtendedTorFamily (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B
            C).toRingHom q M N)
        (fun n ↦ (-1 : ℤ) ^ n) ((middleFiniteSupport k A B C P q hPq M N).mp h) := by
  apply ambientLocalTor_signedLengthSum _
      (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap_surjective k A B C)
      (hPq := hPq)
  · rw [ambientMiddle_leftMap]
    exact _root_.AlgebraicGeometry.Scheme.Products.MiddleDiagonal.leftMap_flat k A B C
  · rw [ambientMiddle_rightMap]
    exact _root_.AlgebraicGeometry.Scheme.Products.MiddleDiagonal.rightMap_flat k A B C

end MotivicTest.TorComparisonAmbientLocalLength
