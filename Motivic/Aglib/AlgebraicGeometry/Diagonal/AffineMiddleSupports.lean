/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Diagonal.AffineMiddle
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual affine support products in the middle-diagonal ambient scheme

Arbitrary quotient ideals define the two adjacent closed support schemes. Their
literal product has coordinate ring the exterior tensor of the two quotients,
and its actual ambient morphism is the spectrum of the tensor of quotient maps.
No support flatness, reducedness, or integrality is imposed.
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
  (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C))

/-- The actual left quotient support in the adjacent affine product. -/
def leftSupportMap : Spec (CommRingCat.of ((A ⊗[k] B) ⧸ I)) ⟶ leftProduct k A B :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (leftIso k A B).hom

/-- The actual right quotient support in the adjacent affine product. -/
def rightSupportMap : Spec (CommRingCat.of ((B ⊗[k] C) ⧸ J)) ⟶ rightProduct k B C :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ (rightIso k B C).hom

instance : IsClosedImmersion (leftSupportMap k A B I) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  unfold leftSupportMap
  infer_instance

instance : IsClosedImmersion (rightSupportMap k B C J) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  unfold rightSupportMap
  infer_instance

/-- The support's inherited base map is its literal quotient-algebra structure map. -/
@[reassoc (attr := simp)] theorem leftSupportMap_base :
    leftSupportMap k A B I ≫ pullback.snd (structureMap k A) (structureMap k B) ≫
      structureMap k B = structureMap k ((A ⊗[k] B) ⧸ I) := by
  simp only [leftSupportMap, Category.assoc, leftIso, Iso.symm_hom,
    pullbackSpecIso_inv_snd_assoc, structureMap, ← Spec.map_comp]
  congr 1
  ext r
  change Ideal.Quotient.mk I (Algebra.TensorProduct.includeRight (algebraMap k B r)) = _
  rw [AlgHom.commutes]
  rfl

/-- The right support inherits the stated quotient-algebra base map. -/
@[reassoc (attr := simp)] theorem rightSupportMap_base :
    rightSupportMap k B C J ≫ pullback.fst (structureMap k B) (structureMap k C) ≫
      structureMap k B = structureMap k ((B ⊗[k] C) ⧸ J) := by
  simp only [rightSupportMap, Category.assoc, rightIso, Iso.symm_hom,
    pullbackSpecIso_inv_fst_assoc, structureMap, ← Spec.map_comp]
  rfl

/-- The literal product of the two quotient supports over the original base. -/
abbrev supportProduct :=
  pullback
    (leftSupportMap k A B I ≫ pullback.snd (structureMap k A) (structureMap k B) ≫ structureMap k B)
    (rightSupportMap k B C J ≫
      pullback.fst (structureMap k B) (structureMap k C) ≫ structureMap k B)

/-- The actual closed support product has the exterior quotient tensor coordinate ring. -/
def supportProductIso :
    Spec (CommRingCat.of (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))) ≅
      supportProduct k A B C I J :=
  (pullbackSpecIso k ((A ⊗[k] B) ⧸ I) ((B ⊗[k] C) ⧸ J)).symm ≪≫
    pullback.congrHom (leftSupportMap_base k A B I).symm (rightSupportMap_base k B C J).symm

/-- The actual product inclusion into the four-factor ambient scheme. -/
def supportInclusion : supportProduct k A B C I J ⟶
    correspondenceIntersectionAmbient (structureMap k A) (structureMap k B) (structureMap k C) :=
  pullback.map _ _ _ _ (leftSupportMap k A B I) (rightSupportMap k B C J)
    (𝟙 (Spec (CommRingCat.of k))) (by simp) (by simp)

instance : IsClosedImmersion (supportInclusion k A B C I J) := by
  unfold supportInclusion
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion (leftSupportMap k A B I)))
    (inferInstanceAs (IsClosedImmersion (rightSupportMap k B C J))) (by simp) (by simp)

/-- The actual affine support-product coordinate map is the tensor of the quotient maps. -/
def supportRingMap : MiddleDiagonal.ambientRing k A B C →ₐ[k]
    (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J)) :=
  Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k J)

/-- The support-product map preserves each pure coordinate tensor literally. -/
@[simp] theorem supportRingMap_tmul (x : A ⊗[k] B) (y : B ⊗[k] C) :
    supportRingMap k A B C I J (x ⊗ₜ[k] y) =
      Ideal.Quotient.mk I x ⊗ₜ[k] Ideal.Quotient.mk J y := rfl

/-- The exterior quotient map is surjective for arbitrary two ideals. -/
theorem supportRingMap_surjective : Function.Surjective (supportRingMap k A B C I J) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨a ⊗ₜ[k] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

/-- The coordinate ring map is the literal actual ambient inclusion of the support product. -/
@[reassoc] theorem supportRingMap_square :
    Spec.map (CommRingCat.ofHom (supportRingMap k A B C I J).toRingHom) ≫
      (ambientIso k A B C).hom =
    (supportProductIso k A B C I J).hom ≫ supportInclusion k A B C I J := by
  apply pullback.hom_ext
  · simp only [Category.assoc, ambientIso_hom_fst, supportInclusion, pullback.map,
      pullback.lift_fst, supportProductIso, Iso.trans_hom, Iso.symm_hom,
      pullback.congrHom_hom, Category.comp_id,
      pullback.lift_fst_assoc, pullbackSpecIso_inv_fst_assoc, leftSupportMap]
    simp only [← Category.assoc, ← Spec.map_comp]
    congr 2
  · simp only [Category.assoc, ambientIso_hom_snd, supportInclusion, pullback.map,
      pullback.lift_snd, supportProductIso, Iso.trans_hom, Iso.symm_hom,
      pullback.congrHom_hom, Category.comp_id,
      pullback.lift_snd_assoc, pullbackSpecIso_inv_snd_assoc, rightSupportMap]
    simp only [← Category.assoc, ← Spec.map_comp]
    congr 2

/-- The actual pullback of the left quotient support to the triple product. -/
abbrev leftPulledSupport :=
  pullback
    (pullback.fst (pullback.snd (structureMap k A) (structureMap k B))
      (pullback.fst (structureMap k B) (structureMap k C))) (leftSupportMap k A B I)

/-- The left pulled-back support has its literal scalar-extension coordinate ring. -/
def leftPulledSupportIso :
    Spec (CommRingCat.of ((MiddleDiagonal.tripleRing k A B C) ⊗[A ⊗[k] B]
      ((A ⊗[k] B) ⧸ I))) ≅ leftPulledSupport k A B C I :=
  (pullbackSpecIso (A ⊗[k] B) (MiddleDiagonal.tripleRing k A B C)
    ((A ⊗[k] B) ⧸ I)).symm ≪≫
    asIso (pullback.map _ _ _ _ (tripleIso k A B C).hom
      (𝟙 (Spec (CommRingCat.of ((A ⊗[k] B) ⧸ I)))) (leftIso k A B).hom
      (by
        have hm : algebraMap (A ⊗[k] B) (MiddleDiagonal.tripleRing k A B C) =
            (MiddleDiagonal.leftMap k A B C).toRingHom := by
          apply RingHom.ext
          intro x
          rfl
        rw [hm]
        exact (tripleIso_hom_fst k A B C).symm)
      (by simp [leftSupportMap]))

/-- The literal inclusion of the left pulled-back support uses its scalar-extension map. -/
@[reassoc] theorem leftPulledSupportIso_fst :
    (leftPulledSupportIso k A B C I).hom ≫
      pullback.fst
        (pullback.fst (pullback.snd (structureMap k A) (structureMap k B))
          (pullback.fst (structureMap k B) (structureMap k C))) (leftSupportMap k A B I) =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
        (tripleIso k A B C).hom := by
  simp only [leftPulledSupportIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    pullback.map, Category.assoc, pullback.lift_fst]
  exact pullbackSpecIso_inv_fst_assoc (A ⊗[k] B) (MiddleDiagonal.tripleRing k A B C)
    ((A ⊗[k] B) ⧸ I) (tripleIso k A B C).hom

/-- The actual pullback of the right quotient support to the triple product. -/
abbrev rightPulledSupport :=
  pullback
    (pullback.snd (pullback.snd (structureMap k A) (structureMap k B))
      (pullback.fst (structureMap k B) (structureMap k C))) (rightSupportMap k B C J)

/-- The right pulled-back support uses precisely the right adjacent scalar map. -/
def rightPulledSupportIso :
    letI : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
      (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
    Spec (CommRingCat.of ((MiddleDiagonal.tripleRing k A B C) ⊗[B ⊗[k] C]
      ((B ⊗[k] C) ⧸ J))) ≅ rightPulledSupport k A B C J := by
  letI : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
    (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
  exact (pullbackSpecIso (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C)
    ((B ⊗[k] C) ⧸ J)).symm ≪≫
    asIso (pullback.map _ _ _ _ (tripleIso k A B C).hom
      (𝟙 (Spec (CommRingCat.of ((B ⊗[k] C) ⧸ J)))) (rightIso k B C).hom
      (tripleIso_hom_snd k A B C).symm
      (by simp [rightSupportMap]))

/-- The right pulled-back support inclusion has the specified scalar-extension coordinate map. -/
@[reassoc] theorem rightPulledSupportIso_fst :
    let : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
      (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
    (rightPulledSupportIso k A B C J).hom ≫
      pullback.fst
        (pullback.snd (pullback.snd (structureMap k A) (structureMap k B))
          (pullback.fst (structureMap k B) (structureMap k C))) (rightSupportMap k B C J) =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
        (tripleIso k A B C).hom := by
  let : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
    (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
  simp only [rightPulledSupportIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    pullback.map, Category.assoc, pullback.lift_fst]
  exact pullbackSpecIso_inv_fst_assoc (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C)
    ((B ⊗[k] C) ⧸ J) (tripleIso k A B C).hom

end AlgebraicGeometry.Scheme.Products.MiddleDiagonal
