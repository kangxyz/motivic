/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Diagonal.AffineMiddleSupportPoints

/-! # Consumers of actual incidence-prime compatibility in all four coordinate rings -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct Motivic.MiddleDiagonal

universe u

namespace Motivic.MotivicTest.AffineMiddleSupportPoints

open Motivic.AffineMiddle

variable (k A B C : Type u) [CommRing k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  (F : FiniteCorrespondenceGenerator (structureMap k A) (structureMap k B))
  (G : FiniteCorrespondenceGenerator (structureMap k B) (structureMap k C))
  (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C))
  (eI : Spec (CommRingCat.of ((A ⊗[k] B) ⧸ I)) ≅ F.scheme)
  (hI : eI.hom ≫ F.inclusion = leftSupportMap k A B I)
  (eJ : Spec (CommRingCat.of ((B ⊗[k] C) ⧸ J)) ≅ G.scheme)
  (hJ : eJ.hom ≫ G.inclusion = rightSupportMap k B C J)
  (e : Spec (CommRingCat.of (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))) ≅
    F.supportProduct G)
  (he : Spec.map (CommRingCat.ofHom (supportRingMap k A B C I J).toRingHom) ≫
    (ambientIso k A B C).hom = e.hom ≫ F.supportProductInclusion G)
  (w : F.incidence G)

include he in
/-- The actual source/coefficient point equality gives the literal common ambient prime. -/
theorem common_ambient_prime :
    (incidenceTriplePrime k A B C F G w).comap (MiddleDiagonal.quotientMap k A B C).toRingHom =
      (incidenceSupportPrime k A B C F G I J e w).comap
        (supportRingMap k A B C I J).toRingHom :=
  incidenceTriplePrime_comap_eq_support k A B C F G I J e he w

/-- Both actual pulled support primes project to the same triple prime. -/
theorem pulled_primes_agree :
    letI : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
      (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
    (incidenceRightPrime k A B C F G J eJ hJ w).comap
        Algebra.TensorProduct.includeLeftRingHom =
      (incidenceLeftPrime k A B C F G I eI hI w).comap
        Algebra.TensorProduct.includeLeftRingHom :=
  (incidenceTriplePrime_eq_right_comap k A B C F G J eJ hJ w).symm.trans
    (incidenceTriplePrime_eq_left_comap k A B C F G I eI hI w)

include he in
/-- Taking the right support's image as the triple prime preserves common ambient localization. -/
theorem right_image_ambient_prime :
    letI : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
      (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
    ((incidenceRightPrime k A B C F G J eJ hJ w).comap
      Algebra.TensorProduct.includeLeftRingHom).comap
        (MiddleDiagonal.quotientMap k A B C).toRingHom =
      (incidenceSupportPrime k A B C F G I J e w).comap
        (supportRingMap k A B C I J).toRingHom := by
  rw [← incidenceTriplePrime_eq_right_comap k A B C F G J eJ hJ w]
  exact incidenceTriplePrime_comap_eq_support k A B C F G I J e he w

end Motivic.MotivicTest.AffineMiddleSupportPoints
