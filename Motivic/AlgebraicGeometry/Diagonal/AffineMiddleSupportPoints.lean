/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Diagonal.AffineMiddlePulledSupports

/-!
# Actual incidence points in the affine support coordinates

An actual incidence point determines primes in the triple ring, support-product
ring and both pulled-support extension rings. The common-ambient-prime equalities
follow from the actual scheme squares, with the left and right scalar maps kept
explicit. No localization or tensor product of local stalks is substituted here.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct Motivic.MiddleDiagonal

universe u

namespace Motivic.AffineMiddle

variable (k A B C : Type u) [CommRing k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  (F : FiniteCorrespondenceGenerator (structureMap k A) (structureMap k B))
  (G : FiniteCorrespondenceGenerator (structureMap k B) (structureMap k C))

/-- The actual incidence map to the left pulled ideal subscheme. -/
def incidenceToLeftPulled : F.incidence G ⟶
    (F.val.comap (pullback.fst (pullback.snd (structureMap k A) (structureMap k B))
      (pullback.fst (structureMap k B) (structureMap k C)))).subscheme :=
  pullback.lift (F.incidenceInclusion G) (F.incidenceFst G) (F.incidenceInclusion_fst G) ≫
    (F.val.comapIso _).inv

/-- The actual left pulled-support map lies above the incidence point of the triple product. -/
@[reassoc (attr := simp)] theorem incidenceToLeftPulled_inclusion :
    incidenceToLeftPulled k A B C F G ≫
      (F.val.comap (pullback.fst (pullback.snd (structureMap k A) (structureMap k B))
        (pullback.fst (structureMap k B) (structureMap k C)))).subschemeι =
      F.incidenceInclusion G := by
  simp [incidenceToLeftPulled]

/-- The actual incidence map to the right pulled ideal subscheme. -/
def incidenceToRightPulled : F.incidence G ⟶
    (G.val.comap (pullback.snd (pullback.snd (structureMap k A) (structureMap k B))
      (pullback.fst (structureMap k B) (structureMap k C)))).subscheme :=
  pullback.lift (F.incidenceInclusion G) (F.incidenceSnd G) (F.incidenceInclusion_snd G) ≫
    (G.val.comapIso _).inv

/-- The actual right pulled-support map lies above the same triple-product point. -/
@[reassoc (attr := simp)] theorem incidenceToRightPulled_inclusion :
    incidenceToRightPulled k A B C F G ≫
      (G.val.comap (pullback.snd (pullback.snd (structureMap k A) (structureMap k B))
        (pullback.fst (structureMap k B) (structureMap k C)))).subschemeι =
      F.incidenceInclusion G := by
  simp [incidenceToRightPulled]

/-- The triple-ring prime corresponding to an actual incidence point. -/
def incidenceTriplePrime (w : F.incidence G) : PrimeSpectrum (MiddleDiagonal.tripleRing k A B C) :=
  (tripleIso k A B C).inv (F.incidenceInclusion G w)

variable (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C))

/-- The support-product prime corresponding to the same actual incidence point. -/
def incidenceSupportPrime
    (e : Spec (CommRingCat.of (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))) ≅
      F.supportProduct G) (w : F.incidence G) :
    PrimeSpectrum (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J)) :=
  e.inv (F.incidenceToSupportProduct G w)

/-- The actual incidence square gives exactly the common ambient coordinate prime. -/
theorem incidenceTriplePrime_comap_eq_support
    (e : Spec (CommRingCat.of (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))) ≅
      F.supportProduct G)
    (he : Spec.map (CommRingCat.ofHom (supportRingMap k A B C I J).toRingHom) ≫
      (ambientIso k A B C).hom = e.hom ≫ F.supportProductInclusion G)
    (w : F.incidence G) :
    (incidenceTriplePrime k A B C F G w).comap (MiddleDiagonal.quotientMap k A B C).toRingHom =
      (incidenceSupportPrime k A B C F G I J e w).comap
        (supportRingMap k A B C I J).toRingHom := by
  apply (Scheme.homeoOfIso (ambientIso k A B C)).injective
  change (Spec.map (CommRingCat.ofHom (MiddleDiagonal.quotientMap k A B C).toRingHom) ≫
      (ambientIso k A B C).hom) (incidenceTriplePrime k A B C F G w) =
    (Spec.map (CommRingCat.ofHom
      (S := ((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))
      (supportRingMap k A B C I J).toRingHom) ≫
      (ambientIso k A B C).hom) (incidenceSupportPrime k A B C F G I J e w)
  rw [quotientMap_square, he]
  simp only [Scheme.Hom.comp_apply, incidenceTriplePrime, incidenceSupportPrime,
    Scheme.inv_hom_apply]
  exact congrArg (fun f ↦ f w) (F.incidence_ambient_comm G)

/-- The actual left pulled-support point in its scalar-extension coordinate ring. -/
def incidenceLeftPrime
    (e : Spec (CommRingCat.of ((A ⊗[k] B) ⧸ I)) ≅ F.scheme)
    (he : e.hom ≫ F.inclusion = leftSupportMap k A B I) (w : F.incidence G) :
    PrimeSpectrum ((MiddleDiagonal.tripleRing k A B C) ⊗[A ⊗[k] B] ((A ⊗[k] B) ⧸ I)) :=
  (leftGeneratorPulledIso k A B C F I e he).inv (incidenceToLeftPulled k A B C F G w)

/-- The left pulled coordinate prime maps to the actual triple coordinate prime. -/
theorem incidenceTriplePrime_eq_left_comap
    (e : Spec (CommRingCat.of ((A ⊗[k] B) ⧸ I)) ≅ F.scheme)
    (he : e.hom ≫ F.inclusion = leftSupportMap k A B I) (w : F.incidence G) :
    incidenceTriplePrime k A B C F G w =
      (incidenceLeftPrime k A B C F G I e he w).comap
        Algebra.TensorProduct.includeLeftRingHom := by
  apply (Scheme.homeoOfIso (tripleIso k A B C)).injective
  change (tripleIso k A B C).hom (incidenceTriplePrime k A B C F G w) =
    (Spec.map (CommRingCat.ofHom
      (S := (MiddleDiagonal.tripleRing k A B C) ⊗[A ⊗[k] B] ((A ⊗[k] B) ⧸ I))
      Algebra.TensorProduct.includeLeftRingHom) ≫
      (tripleIso k A B C).hom) (incidenceLeftPrime k A B C F G I e he w)
  rw [← leftGeneratorPulledIso_inclusion k A B C F I e he]
  simp only [Scheme.Hom.comp_apply, incidenceTriplePrime, incidenceLeftPrime,
    Scheme.inv_hom_apply]
  exact (congrArg (fun f ↦ f w) (incidenceToLeftPulled_inclusion k A B C F G)).symm

/-- The actual right pulled-support point in its specified right scalar-extension ring. -/
def incidenceRightPrime
    (e : Spec (CommRingCat.of ((B ⊗[k] C) ⧸ J)) ≅ G.scheme)
    (he : e.hom ≫ G.inclusion = rightSupportMap k B C J) (w : F.incidence G) :
    letI : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
      (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
    PrimeSpectrum ((MiddleDiagonal.tripleRing k A B C) ⊗[B ⊗[k] C] ((B ⊗[k] C) ⧸ J)) :=
  (rightGeneratorPulledIso k A B C G J e he).inv (incidenceToRightPulled k A B C F G w)

/-- The right pulled coordinate prime maps to the same actual triple coordinate prime. -/
theorem incidenceTriplePrime_eq_right_comap
    (e : Spec (CommRingCat.of ((B ⊗[k] C) ⧸ J)) ≅ G.scheme)
    (he : e.hom ≫ G.inclusion = rightSupportMap k B C J) (w : F.incidence G) :
    letI : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
      (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
    incidenceTriplePrime k A B C F G w =
      (incidenceRightPrime k A B C F G J e he w).comap
        Algebra.TensorProduct.includeLeftRingHom := by
  let : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
    (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
  apply (Scheme.homeoOfIso (tripleIso k A B C)).injective
  change (tripleIso k A B C).hom (incidenceTriplePrime k A B C F G w) =
    (Spec.map (CommRingCat.ofHom
      (S := (MiddleDiagonal.tripleRing k A B C) ⊗[B ⊗[k] C] ((B ⊗[k] C) ⧸ J))
      Algebra.TensorProduct.includeLeftRingHom) ≫
      (tripleIso k A B C).hom) (incidenceRightPrime k A B C F G J e he w)
  rw [← rightGeneratorPulledIso_inclusion k A B C G J e he]
  simp only [Scheme.Hom.comp_apply, incidenceTriplePrime, incidenceRightPrime,
    Scheme.inv_hom_apply]
  exact (congrArg (fun f ↦ f w) (incidenceToRightPulled_inclusion k A B C F G)).symm

end Motivic.AffineMiddle
