/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Diagonal.AffineSupportPresentation

public import Motivic.Aglib.AlgebraicGeometry.Diagonal.AffineMiddleSupports
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Intersection.Ambient

/-!
# Quotient coordinates for actual correspondence supports

Closed immersions into the adjacent affine products possess actual quotient
presentations. Applying them to the library's finite-correspondence generators
identifies their literal support product and ambient inclusion with the exterior
quotient tensor coordinate presentation. The presentations are constructed from
closed immersions; they are not additional hypotheses.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct Algebra.TensorProduct.MiddleDiagonal

universe u

namespace AlgebraicGeometry.Scheme.Products.MiddleDiagonal

variable (k A B C : Type u) [CommRing k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

variable
  (F : _root_.Motivic.FiniteCorrespondenceGenerator (structureMap k A) (structureMap k B))
  (G : _root_.Motivic.FiniteCorrespondenceGenerator (structureMap k B) (structureMap k C))

/-- Actual finite-correspondence support products admit the exterior quotient tensor presentation,
with the exact ambient scalar map. -/
theorem exists_generatorSupportProductPresentation :
    ∃ I : Ideal (A ⊗[k] B), ∃ J : Ideal (B ⊗[k] C),
    ∃ eI : Spec (CommRingCat.of ((A ⊗[k] B) ⧸ I)) ≅ F.scheme,
    ∃ eJ : Spec (CommRingCat.of ((B ⊗[k] C) ⧸ J)) ≅ G.scheme,
      eI.hom ≫ F.inclusion = leftSupportMap k A B I ∧
      eJ.hom ≫ G.inclusion = rightSupportMap k B C J ∧
    ∃ e : Spec (CommRingCat.of (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))) ≅
      F.supportProduct G,
      Spec.map (CommRingCat.ofHom (supportRingMap k A B C I J).toRingHom) ≫
        (ambientIso k A B C).hom = e.hom ≫ F.supportProductInclusion G := by
  obtain ⟨I, eI, hI⟩ := exists_leftSupportPresentation k A B F.inclusion
  obtain ⟨J, eJ, hJ⟩ := exists_rightSupportPresentation k B C G.inclusion
  let e : supportProduct k A B C I J ≅ F.supportProduct G :=
    asIso (pullback.map _ _ _ _ eI.hom eJ.hom (𝟙 (Spec (CommRingCat.of k)))
      (by
        simpa only [Category.comp_id, _root_.Motivic.FiniteCorrespondenceGenerator.targetProjection,
          Category.assoc] using
          congrArg (fun t ↦ t ≫ pullback.snd (structureMap k A) (structureMap k B) ≫
            structureMap k B) hI.symm)
      (by
        simpa only [Category.comp_id, _root_.Motivic.FiniteCorrespondenceGenerator.projection,
          _root_.Motivic.correspondenceProjection, Category.assoc] using
          congrArg (fun t ↦ t ≫ pullback.fst (structureMap k B) (structureMap k C) ≫
            structureMap k B) hJ.symm))
  refine ⟨I, J, eI, eJ, hI, hJ, supportProductIso k A B C I J ≪≫ e, ?_⟩
  rw [supportRingMap_square, Iso.trans_hom, Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [supportInclusion, pullback.map, pullback.lift_fst, Category.assoc,
      _root_.Motivic.FiniteCorrespondenceGenerator.supportProductInclusion_fst, e, asIso_hom,
      pullback.lift_fst_assoc]
    exact congrArg (fun t ↦ pullback.fst _ _ ≫ t) hI.symm
  · simp only [supportInclusion, pullback.map, pullback.lift_snd, Category.assoc,
      _root_.Motivic.FiniteCorrespondenceGenerator.supportProductInclusion_snd, e, asIso_hom,
      pullback.lift_snd_assoc]
    exact congrArg (fun t ↦ pullback.snd _ _ ≫ t) hJ.symm

end AlgebraicGeometry.Scheme.Products.MiddleDiagonal
