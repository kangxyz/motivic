/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Diagonal.AffineMiddleCorrespondenceSupports

/-!
# Actual pulled-back correspondence supports in affine quotient coordinates

The quotient charts constructed for actual closed correspondence supports give
literal scalar-extension coordinate presentations of their pulled-back ideal
subschemes in the triple product. Both inclusion squares use the corresponding
left or right adjacent scalar map.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct Algebra.TensorProduct.MiddleDiagonal

universe u

namespace AlgebraicGeometry.Scheme.Products.MiddleDiagonal
open _root_.Algebra.TensorProduct

variable (k A B C : Type u) [CommRing k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  (F : _root_.Motivic.FiniteCorrespondenceGenerator (structureMap k A) (structureMap k B))
  (G : _root_.Motivic.FiniteCorrespondenceGenerator (structureMap k B) (structureMap k C))

/-- A quotient chart gives the actual scalar-extension presentation of the left pulled support. -/
def leftGeneratorPulledIso (I : Ideal (A ⊗[k] B))
    (e : Spec (CommRingCat.of ((A ⊗[k] B) ⧸ I)) ≅ F.scheme)
    (he : e.hom ≫ F.inclusion = leftSupportMap k A B I) :
    Spec (CommRingCat.of ((MiddleDiagonal.tripleRing k A B C) ⊗[A ⊗[k] B]
      ((A ⊗[k] B) ⧸ I))) ≅
    (F.val.comap (pullback.fst (pullback.snd (structureMap k A) (structureMap k B))
      (pullback.fst (structureMap k B) (structureMap k C)))).subscheme :=
  leftPulledSupportIso k A B C I ≪≫
    asIso (pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _) (by simp) (by simpa using he.symm)) ≪≫
    (F.val.comapIso _).symm

/-- The actual left pulled ideal-subscheme inclusion has the scalar-extension coordinate map. -/
@[reassoc] theorem leftGeneratorPulledIso_inclusion (I : Ideal (A ⊗[k] B))
    (e : Spec (CommRingCat.of ((A ⊗[k] B) ⧸ I)) ≅ F.scheme)
    (he : e.hom ≫ F.inclusion = leftSupportMap k A B I) :
    (leftGeneratorPulledIso k A B C F I e he).hom ≫
      (F.val.comap (pullback.fst (pullback.snd (structureMap k A) (structureMap k B))
        (pullback.fst (structureMap k B) (structureMap k C)))).subschemeι =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
        (tripleIso k A B C).hom := by
  simp only [leftGeneratorPulledIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Scheme.IdealSheafData.comapIso_inv_subschemeι, asIso_hom, pullback.map,
    pullback.lift_fst, Category.comp_id, leftPulledSupportIso_fst]

/-- A quotient chart gives the actual scalar-extension presentation of the right pulled support. -/
def rightGeneratorPulledIso (J : Ideal (B ⊗[k] C))
    (e : Spec (CommRingCat.of ((B ⊗[k] C) ⧸ J)) ≅ G.scheme)
    (he : e.hom ≫ G.inclusion = rightSupportMap k B C J) :
    letI : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
      (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
    Spec (CommRingCat.of ((MiddleDiagonal.tripleRing k A B C) ⊗[B ⊗[k] C]
      ((B ⊗[k] C) ⧸ J))) ≅
    (G.val.comap (pullback.snd (pullback.snd (structureMap k A) (structureMap k B))
      (pullback.fst (structureMap k B) (structureMap k C)))).subscheme := by
  letI : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
    (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
  exact rightPulledSupportIso k A B C J ≪≫
    asIso (pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _) (by simp) (by simpa using he.symm)) ≪≫
    (G.val.comapIso _).symm

/-- The actual right pulled ideal-subscheme inclusion has the specified coordinate map. -/
@[reassoc] theorem rightGeneratorPulledIso_inclusion (J : Ideal (B ⊗[k] C))
    (e : Spec (CommRingCat.of ((B ⊗[k] C) ⧸ J)) ≅ G.scheme)
    (he : e.hom ≫ G.inclusion = rightSupportMap k B C J) :
    letI : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
      (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
    (rightGeneratorPulledIso k A B C G J e he).hom ≫
      (G.val.comap (pullback.snd (pullback.snd (structureMap k A) (structureMap k B))
        (pullback.fst (structureMap k B) (structureMap k C)))).subschemeι =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
        (tripleIso k A B C).hom := by
  simp only [rightGeneratorPulledIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Scheme.IdealSheafData.comapIso_inv_subschemeι, asIso_hom, pullback.map,
    pullback.lift_fst, Category.comp_id, rightPulledSupportIso_fst]

end AlgebraicGeometry.Scheme.Products.MiddleDiagonal
