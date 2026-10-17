/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.TensorProduct.MiddleDiagonal
public import Motivic.AlgebraicGeometry.Correspondences.IntersectionAmbientIdeal
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual affine coordinates for the middle-diagonal inclusion

The actual four-factor ambient scheme and triple product are identified with
spectra of their coordinate tensor rings. The literal triple inclusion is the
spectrum of the surjective coordinate map identifying the middle actions.
All projection squares retain the specified scalar maps.
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

/-- The affine structure map of a coordinate algebra. -/
abbrev structureMap (D : Type u) [CommRing D] [Algebra k D] :
    Spec (CommRingCat.of D) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k D))

/-- The actual adjacent left fiber product. -/
abbrev leftProduct := pullback (structureMap k A) (structureMap k B)

/-- The actual adjacent right fiber product. -/
abbrev rightProduct := pullback (structureMap k B) (structureMap k C)

/-- The coordinate isomorphism of the left adjacent product. -/
abbrev leftIso : Spec (CommRingCat.of (A ⊗[k] B)) ≅ leftProduct k A B :=
  (pullbackSpecIso k A B).symm

/-- The coordinate isomorphism of the right adjacent product. -/
abbrev rightIso : Spec (CommRingCat.of (B ⊗[k] C)) ≅ rightProduct k B C :=
  (pullbackSpecIso k B C).symm

/-- The actual four-factor ambient scheme in affine coordinates. -/
def ambientIso : Spec (CommRingCat.of (MiddleDiagonal.ambientRing k A B C)) ≅
    correspondenceIntersectionAmbient (structureMap k A) (structureMap k B)
      (structureMap k C) :=
  (pullbackSpecIso k (A ⊗[k] B) (B ⊗[k] C)).symm ≪≫
    asIso (pullback.map _ _ _ _ (leftIso k A B).hom (rightIso k B C).hom
      (𝟙 (Spec (CommRingCat.of k))) (by
        simp only [Category.comp_id, leftIso, Iso.symm_hom,
          pullbackSpecIso_inv_snd_assoc, structureMap, ← Spec.map_comp]
        congr 1
        ext r
        exact (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).commutes r |>.symm)
      (by
        simp only [Category.comp_id, rightIso, Iso.symm_hom,
          pullbackSpecIso_inv_fst_assoc, structureMap, ← Spec.map_comp]
        rfl))

/-- The actual triple scheme in coordinates balanced over its middle algebra. -/
def tripleIso : Spec (CommRingCat.of (MiddleDiagonal.tripleRing k A B C)) ≅
    correspondenceTripleProduct (structureMap k A) (structureMap k B) (structureMap k C) :=
  (pullbackSpecIso B (A ⊗[k] B) (B ⊗[k] C)).symm ≪≫
    asIso (pullback.map _ _ _ _ (leftIso k A B).hom (rightIso k B C).hom
      (𝟙 (Spec (CommRingCat.of B))) (by
        simp only [Category.comp_id, leftIso, Iso.symm_hom, pullbackSpecIso_inv_snd]
        rfl)
      (by
        simp only [Category.comp_id, rightIso, Iso.symm_hom, pullbackSpecIso_inv_fst]
        rfl))

/-- The first ambient projection is induced by the literal left tensor inclusion. -/
@[reassoc (attr := simp)] theorem ambientIso_hom_fst :
    (ambientIso k A B C).hom ≫
      pullback.fst (pullback.snd (structureMap k A) (structureMap k B) ≫ structureMap k B)
        (pullback.fst (structureMap k B) (structureMap k C) ≫ structureMap k B) =
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
      (leftIso k A B).hom := by
  simp [ambientIso, pullback.map]

/-- The second ambient projection is induced by the literal right tensor inclusion. -/
@[reassoc (attr := simp)] theorem ambientIso_hom_snd :
    (ambientIso k A B C).hom ≫
      pullback.snd (pullback.snd (structureMap k A) (structureMap k B) ≫ structureMap k B)
        (pullback.fst (structureMap k B) (structureMap k C) ≫ structureMap k B) =
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
      (rightIso k B C).hom := by
  simp [ambientIso, pullback.map]

/-- The first triple projection is induced by the specified left scalar map. -/
@[reassoc (attr := simp)] theorem tripleIso_hom_fst :
    (tripleIso k A B C).hom ≫
      pullback.fst (pullback.snd (structureMap k A) (structureMap k B))
        (pullback.fst (structureMap k B) (structureMap k C)) =
    Spec.map (CommRingCat.ofHom (MiddleDiagonal.leftMap k A B C).toRingHom) ≫
      (leftIso k A B).hom := by
  simp [tripleIso, pullback.map, MiddleDiagonal.leftMap]
  rfl

/-- The second triple projection is induced by the specified right scalar map. -/
@[reassoc (attr := simp)] theorem tripleIso_hom_snd :
    (tripleIso k A B C).hom ≫
      pullback.snd (pullback.snd (structureMap k A) (structureMap k B))
        (pullback.fst (structureMap k B) (structureMap k C)) =
    Spec.map (CommRingCat.ofHom (MiddleDiagonal.rightMap k A B C).toRingHom) ≫
      (rightIso k B C).hom := by
  simp [tripleIso, pullback.map, MiddleDiagonal.rightMap]

/-- The actual middle-diagonal inclusion is the spectrum of the coordinate quotient. -/
@[reassoc] theorem quotientMap_square :
    Spec.map (CommRingCat.ofHom (MiddleDiagonal.quotientMap k A B C).toRingHom) ≫
      (ambientIso k A B C).hom =
    (tripleIso k A B C).hom ≫
      correspondenceTripleInclusion (structureMap k A) (structureMap k B) (structureMap k C) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, ambientIso_hom_fst,
      correspondenceTripleInclusion_fst, tripleIso_hom_fst]
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    exact congrArg (fun f => CommRingCat.ofHom f.toRingHom)
      (MiddleDiagonal.quotientMap_comp_left k A B C)
  · simp only [Category.assoc, ambientIso_hom_snd,
      correspondenceTripleInclusion_snd, tripleIso_hom_snd]
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    exact congrArg (fun f => CommRingCat.ofHom f.toRingHom)
      (MiddleDiagonal.quotientMap_comp_right k A B C)

end Motivic.AffineMiddle
