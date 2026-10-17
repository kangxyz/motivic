/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Diagonal.AffineMiddlePulledSupports

/-! # Consumers of actual exterior quotient support coordinates and pulled ideal subschemes -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct Motivic.MiddleDiagonal

universe u

namespace Motivic.MotivicTest.AffineMiddleSupports

open Motivic.AffineMiddle

variable (k A B C : Type u) [CommRing k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C))

/-- The actual support-product coordinate map is surjective for arbitrary ideals. -/
theorem onto : Function.Surjective (supportRingMap k A B C I J) :=
  supportRingMap_surjective k A B C I J

/-- The actual quotient support product is a closed subscheme of the four-factor ambient scheme. -/
theorem closed_support : IsClosedImmersion (supportInclusion k A B C I J) := inferInstance

/-- The literal actual support-product inclusion has the tensor quotient coordinate map. -/
theorem actual_product_square :
    Spec.map (CommRingCat.ofHom (supportRingMap k A B C I J).toRingHom) ≫
      (ambientIso k A B C).hom =
    (supportProductIso k A B C I J).hom ≫ supportInclusion k A B C I J :=
  supportRingMap_square k A B C I J

/-- The actual left pulled support has the scalar-extension coordinate ring. -/
def leftPullback :
    Spec (CommRingCat.of ((MiddleDiagonal.tripleRing k A B C) ⊗[A ⊗[k] B]
      ((A ⊗[k] B) ⧸ I))) ≅ leftPulledSupport k A B C I :=
  leftPulledSupportIso k A B C I

/-- The actual right pulled support uses the specified right adjacent algebra structure. -/
def rightPullback :
    letI : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
      (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
    Spec (CommRingCat.of ((MiddleDiagonal.tripleRing k A B C) ⊗[B ⊗[k] C]
      ((B ⊗[k] C) ⧸ J))) ≅ rightPulledSupport k A B C J :=
  rightPulledSupportIso k A B C J

variable
  (F : FiniteCorrespondenceGenerator (structureMap k A) (structureMap k B))
  (G : FiniteCorrespondenceGenerator (structureMap k B) (structureMap k C))

/-- The actual generator support product has the proved tensor quotient presentation. -/
theorem actual_product_chart :
    ∃ I : Ideal (A ⊗[k] B), ∃ J : Ideal (B ⊗[k] C),
    ∃ e : Spec (CommRingCat.of (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))) ≅
      F.supportProduct G,
      Spec.map (CommRingCat.ofHom (supportRingMap k A B C I J).toRingHom) ≫
        (ambientIso k A B C).hom = e.hom ≫ F.supportProductInclusion G := by
  obtain ⟨I, J, _, _, _, _, e, he⟩ :=
    exists_generatorSupportProductPresentation k A B C F G
  exact ⟨I, J, e, he⟩

/-- Quotient charts for an actual generator are proved from its closed immersion. -/
theorem actual_left_chart :
    ∃ I : Ideal (A ⊗[k] B), ∃ e : Spec (CommRingCat.of ((A ⊗[k] B) ⧸ I)) ≅ F.scheme,
      e.hom ≫ F.inclusion = leftSupportMap k A B I :=
  exists_leftSupportPresentation k A B F.inclusion

/-- A constructed quotient chart identifies the actual pulled-back left ideal subscheme. -/
def actualLeftPullback
    (e : Spec (CommRingCat.of ((A ⊗[k] B) ⧸ I)) ≅ F.scheme)
    (he : e.hom ≫ F.inclusion = leftSupportMap k A B I) :
    Spec (CommRingCat.of ((MiddleDiagonal.tripleRing k A B C) ⊗[A ⊗[k] B]
      ((A ⊗[k] B) ⧸ I))) ≅
    (F.val.comap (pullback.fst (pullback.snd (structureMap k A) (structureMap k B))
      (pullback.fst (structureMap k B) (structureMap k C)))).subscheme :=
  leftGeneratorPulledIso k A B C F I e he

/-- A constructed quotient chart identifies the actual pulled-back right ideal subscheme. -/
def actualRightPullback
    (e : Spec (CommRingCat.of ((B ⊗[k] C) ⧸ J)) ≅ G.scheme)
    (he : e.hom ≫ G.inclusion = rightSupportMap k B C J) :
    letI : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
      (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
    Spec (CommRingCat.of ((MiddleDiagonal.tripleRing k A B C) ⊗[B ⊗[k] C]
      ((B ⊗[k] C) ⧸ J))) ≅
    (G.val.comap (pullback.snd (pullback.snd (structureMap k A) (structureMap k B))
      (pullback.fst (structureMap k B) (structureMap k C)))).subscheme :=
  rightGeneratorPulledIso k A B C G J e he

end Motivic.MotivicTest.AffineMiddleSupports
