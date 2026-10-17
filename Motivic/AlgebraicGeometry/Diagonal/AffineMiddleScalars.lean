/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Diagonal.AffineMiddle

/-!
# The actual middle-coordinate square and flat adjacent scalar maps

The explicit affine presentation respects the map to the middle self-product
and its diagonal. Flatness of each adjacent-to-triple scalar map follows from
flatness of the remaining outer factor, using the actual scheme pullbacks.
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

/-- The actual triple scheme also has its ordinary three-factor tensor presentation. -/
def ordinaryTripleIso : Spec (CommRingCat.of ((A ⊗[k] B) ⊗[k] C)) ≅
    correspondenceTripleProduct (structureMap k A) (structureMap k B) (structureMap k C) :=
  Scheme.Spec.mapIso (MiddleDiagonal.tripleEquiv k A B C).toRingEquiv.toCommRingCatIso.op ≪≫
    tripleIso k A B C

/-- The actual inclusion and its coordinate quotient are isomorphic as arrows. -/
def inclusionArrowIso :
    Arrow.mk (Spec.map (CommRingCat.ofHom (MiddleDiagonal.quotientMap k A B C).toRingHom)) ≅
      Arrow.mk (correspondenceTripleInclusion (structureMap k A)
        (structureMap k B) (structureMap k C)) :=
  Arrow.isoMk (tripleIso k A B C) (ambientIso k A B C) (quotientMap_square k A B C).symm

/-- The actual ambient-to-middle-pair map is the spectrum of both middle inclusions. -/
@[reassoc] theorem middlePair_square :
    Spec.map (CommRingCat.ofHom (MiddleDiagonal.middlePairMap k A B C).toRingHom) ≫
      (pullbackSpecIso k B B).inv =
    (ambientIso k A B C).hom ≫
      correspondenceMiddlePair (structureMap k A) (structureMap k B) (structureMap k C) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSpecIso_inv_fst, correspondenceMiddlePair_fst,
      ambientIso_hom_fst_assoc, leftIso, Iso.symm_hom, pullbackSpecIso_inv_snd]
    simp only [← Spec.map_comp]
    rfl
  · simp only [Category.assoc, pullbackSpecIso_inv_snd, correspondenceMiddlePair_snd,
      ambientIso_hom_snd_assoc, rightIso, Iso.symm_hom, pullbackSpecIso_inv_fst]
    simp only [← Spec.map_comp]
    rfl

/-- The middle coordinate of the actual triple is the specified balanced scalar map. -/
@[reassoc] theorem middle_square :
    Spec.map (CommRingCat.ofHom (MiddleDiagonal.middleMap k A B C).toRingHom) =
      (tripleIso k A B C).hom ≫
        correspondenceTripleMiddle (structureMap k A) (structureMap k B) (structureMap k C) := by
  simp only [correspondenceTripleMiddle, tripleIso_hom_fst_assoc, leftIso,
    Iso.symm_hom, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  rfl

/-- The first adjacent scalar map is flat when the remaining right outer algebra is flat. -/
theorem leftMap_flat [Module.Flat k C] : (MiddleDiagonal.leftMap k A B C).toRingHom.Flat := by
  have : Flat (structureMap k C) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  apply (Flat.SpecMap_iff (f := CommRingCat.ofHom
    (MiddleDiagonal.leftMap k A B C).toRingHom)).mp
  have heq : Spec.map (CommRingCat.ofHom (MiddleDiagonal.leftMap k A B C).toRingHom) =
      ((tripleIso k A B C).hom ≫
        pullback.fst (pullback.snd (structureMap k A) (structureMap k B))
          (pullback.fst (structureMap k B) (structureMap k C))) ≫ (leftIso k A B).inv := by
    rw [tripleIso_hom_fst, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

/-- The second adjacent scalar map is flat when the remaining left outer algebra is flat. -/
theorem rightMap_flat [Module.Flat k A] : (MiddleDiagonal.rightMap k A B C).toRingHom.Flat := by
  have : Flat (structureMap k A) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  apply (Flat.SpecMap_iff (f := CommRingCat.ofHom
    (MiddleDiagonal.rightMap k A B C).toRingHom)).mp
  have heq : Spec.map (CommRingCat.ofHom (MiddleDiagonal.rightMap k A B C).toRingHom) =
      ((tripleIso k A B C).hom ≫
        pullback.snd (pullback.snd (structureMap k A) (structureMap k B))
          (pullback.fst (structureMap k B) (structureMap k C))) ≫ (rightIso k B C).inv := by
    rw [tripleIso_hom_snd, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

end Motivic.AffineMiddle
