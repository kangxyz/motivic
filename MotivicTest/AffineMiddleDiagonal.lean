/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Diagonal.AffineMiddleScalars
public import Motivic.AlgebraicGeometry.Intersection.ClosedSpecTor
public import Motivic.Algebra.Homology.TorComparison.MixedBase

/-! # Consumers of actual affine middle-diagonal coordinates and closed stalk localization -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct Motivic.MiddleDiagonal

universe u

namespace Motivic.MotivicTest.AffineMiddleDiagonal

variable (k A B C : Type u) [CommRing k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

/-- The coordinate quotient is available without domain or reducedness assumptions. -/
theorem onto : Function.Surjective (MiddleDiagonal.quotientMap k A B C) :=
  MiddleDiagonal.quotientMap_surjective k A B C

/-- The ordinary triple tensor coordinates carry precisely middle multiplication. -/
theorem middle_formula (a : A) (b b' : B) (c : C) :
    MiddleDiagonal.tripleEquiv k A B C
      (MiddleDiagonal.quotientMap k A B C ((a ⊗ₜ[k] b) ⊗ₜ[k] (b' ⊗ₜ[k] c))) =
      (a ⊗ₜ[k] (b * b')) ⊗ₜ[k] c :=
  MiddleDiagonal.tripleEquiv_quotientMap_tmul k A B C a b b' c

/-- The mixed-base comparison uses exactly the affine left scalar map. -/
theorem mixed_left :
    TorComparison.MixedBase.leftMap k (A ⊗[k] B) (B ⊗[k] C)
      (MiddleDiagonal.tripleRing k A B C) (MiddleDiagonal.quotientMap k A B C).toRingHom =
      (MiddleDiagonal.leftMap k A B C).toRingHom :=
  congrArg AlgHom.toRingHom (MiddleDiagonal.quotientMap_comp_left k A B C)

/-- The mixed-base comparison uses exactly the affine right scalar map. -/
theorem mixed_right :
    TorComparison.MixedBase.rightMap k (A ⊗[k] B) (B ⊗[k] C)
      (MiddleDiagonal.tripleRing k A B C) (MiddleDiagonal.quotientMap k A B C).toRingHom =
      (MiddleDiagonal.rightMap k A B C).toRingHom :=
  congrArg AlgHom.toRingHom (MiddleDiagonal.quotientMap_comp_right k A B C)

/-- The actual scheme inclusion is the spectrum of the coordinate quotient. -/
theorem actual_inclusion :
    Spec.map (CommRingCat.ofHom (MiddleDiagonal.quotientMap k A B C).toRingHom) ≫
      (AffineMiddle.ambientIso k A B C).hom =
    (AffineMiddle.tripleIso k A B C).hom ≫
      correspondenceTripleInclusion (AffineMiddle.structureMap k A)
        (AffineMiddle.structureMap k B) (AffineMiddle.structureMap k C) :=
  AffineMiddle.quotientMap_square k A B C

/-- Flatness of the remaining right outer factor gives the actual left scalar flatness. -/
theorem left_flat [Module.Flat k C] : (MiddleDiagonal.leftMap k A B C).toRingHom.Flat :=
  AffineMiddle.leftMap_flat k A B C

/-- Flatness of the remaining left outer factor gives the actual right scalar flatness. -/
theorem right_flat [Module.Flat k A] : (MiddleDiagonal.rightMap k A B C).toRingHom.Flat :=
  AffineMiddle.rightMap_flat k A B C

/-- The closed affine source module really is its ambient-prime localization. -/
def localizedTriple (p : PrimeSpectrum (MiddleDiagonal.tripleRing k A B C)) :
    ModuleCat.of
      (Localization.AtPrime (p.comap (MiddleDiagonal.quotientMap k A B C).toRingHom).asIdeal)
      (LocalizedModule
        (p.comap (MiddleDiagonal.quotientMap k A B C).toRingHom).asIdeal.primeCompl
        (Intersection.specCoordinateModule (MiddleDiagonal.quotientMap k A B C).toRingHom)) ≅
    Intersection.specSourceLocalModule (MiddleDiagonal.quotientMap k A B C).toRingHom p :=
  Intersection.closedSourceLocalizedModuleIso (MiddleDiagonal.quotientMap k A B C).toRingHom
    (MiddleDiagonal.quotientMap_surjective k A B C) p

end Motivic.MotivicTest.AffineMiddleDiagonal
