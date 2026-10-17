/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Diagonal.AffineMiddlePulledSupports

/-!
# Actual tensor coordinates for arbitrary adjacent closed supports

The actual closed supports need not be finite correspondences. Their quotient
charts, exterior support-product chart and scalar-extension pulled-support
charts retain the precise ambient and triple-product inclusion squares.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct Motivic.MiddleDiagonal

universe u

namespace Motivic.AffineMiddle.ClosedSupport

variable (k A B C : Type u) [CommRing k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  {D E : Scheme.{u}} (a : D ⟶ leftProduct k A B) (b : E ⟶ rightProduct k B C)

/-- The genuine product of arbitrary adjacent closed support schemes. -/
abbrev supportProduct : Scheme.{u} :=
  pullback (a ≫ pullback.snd (structureMap k A) (structureMap k B) ≫ structureMap k B)
    (b ≫ pullback.fst (structureMap k B) (structureMap k C) ≫ structureMap k B)

/-- The literal exterior support inclusion in the four-factor ambient scheme. -/
def supportInclusion : supportProduct k A B C a b ⟶
    correspondenceIntersectionAmbient (structureMap k A) (structureMap k B) (structureMap k C) :=
  pullback.map _ _ _ _ a b (𝟙 (Spec (CommRingCat.of k))) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
instance [IsClosedImmersion a] [IsClosedImmersion b] :
    IsClosedImmersion (supportInclusion k A B C a b) := by
  unfold supportInclusion
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion a)) (inferInstanceAs (IsClosedImmersion b)) rfl rfl

/-- Both quotient charts and the actual tensor-product chart are constructed
from the original closed immersions, without any generator premise. -/
theorem exists_supportProductPresentation [IsClosedImmersion a] [IsClosedImmersion b] :
    ∃ I : Ideal (A ⊗[k] B), ∃ J : Ideal (B ⊗[k] C),
    ∃ eI : Spec (CommRingCat.of ((A ⊗[k] B) ⧸ I)) ≅ D,
    ∃ eJ : Spec (CommRingCat.of ((B ⊗[k] C) ⧸ J)) ≅ E,
      eI.hom ≫ a = leftSupportMap k A B I ∧
      eJ.hom ≫ b = rightSupportMap k B C J ∧
    ∃ e : Spec (CommRingCat.of (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))) ≅
      supportProduct k A B C a b,
      Spec.map (CommRingCat.ofHom (supportRingMap k A B C I J).toRingHom) ≫
        (ambientIso k A B C).hom = e.hom ≫ supportInclusion k A B C a b := by
  obtain ⟨I, eI, hI⟩ := exists_leftSupportPresentation k A B a
  obtain ⟨J, eJ, hJ⟩ := exists_rightSupportPresentation k B C b
  let e : AffineMiddle.supportProduct k A B C I J ≅ supportProduct k A B C a b :=
    asIso (pullback.map _ _ _ _ eI.hom eJ.hom (𝟙 (Spec (CommRingCat.of k)))
      (by
        simpa only [Category.comp_id, Category.assoc] using
          congrArg (fun t ↦ t ≫ pullback.snd (structureMap k A) (structureMap k B) ≫
            structureMap k B) hI.symm)
      (by
        simpa only [Category.comp_id, Category.assoc] using
          congrArg (fun t ↦ t ≫ pullback.fst (structureMap k B) (structureMap k C) ≫
            structureMap k B) hJ.symm))
  refine ⟨I, J, eI, eJ, hI, hJ, supportProductIso k A B C I J ≪≫ e, ?_⟩
  rw [supportRingMap_square, Iso.trans_hom, Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [AffineMiddle.supportInclusion, supportInclusion, pullback.map,
      pullback.lift_fst, Category.assoc, e, asIso_hom, pullback.lift_fst_assoc]
    exact congrArg (fun t ↦ pullback.fst _ _ ≫ t) hI.symm
  · simp only [AffineMiddle.supportInclusion, supportInclusion, pullback.map,
      pullback.lift_snd, Category.assoc, e, asIso_hom, pullback.lift_snd_assoc]
    exact congrArg (fun t ↦ pullback.snd _ _ ≫ t) hJ.symm

/-- The actual inverse image of the arbitrary left support in the triple product. -/
abbrev leftPulled : Scheme.{u} :=
  pullback (pullback.fst (pullback.snd (structureMap k A) (structureMap k B))
    (pullback.fst (structureMap k B) (structureMap k C))) a

/-- The actual inverse image of the arbitrary right support in the triple product. -/
abbrev rightPulled : Scheme.{u} :=
  pullback (pullback.snd (pullback.snd (structureMap k A) (structureMap k B))
    (pullback.fst (structureMap k B) (structureMap k C))) b

/-- The left scalar-extension chart is an isomorphism to the actual pulled support. -/
def leftPulledIso (I : Ideal (A ⊗[k] B))
    (e : Spec (CommRingCat.of ((A ⊗[k] B) ⧸ I)) ≅ D)
    (he : e.hom ≫ a = leftSupportMap k A B I) :
    Spec (CommRingCat.of ((MiddleDiagonal.tripleRing k A B C) ⊗[A ⊗[k] B]
      ((A ⊗[k] B) ⧸ I))) ≅ leftPulled k A B C a :=
  leftPulledSupportIso k A B C I ≪≫
    asIso (pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _) (by simp) (by simpa using he.symm))

/-- The right scalar-extension chart retains the specified middle-algebra action. -/
def rightPulledIso (J : Ideal (B ⊗[k] C))
    (e : Spec (CommRingCat.of ((B ⊗[k] C) ⧸ J)) ≅ E)
    (he : e.hom ≫ b = rightSupportMap k B C J) :
    letI : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
      (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
    Spec (CommRingCat.of ((MiddleDiagonal.tripleRing k A B C) ⊗[B ⊗[k] C]
      ((B ⊗[k] C) ⧸ J))) ≅ rightPulled k A B C b := by
  letI : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
    (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
  exact rightPulledSupportIso k A B C J ≪≫
    asIso (pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _) (by simp) (by simpa using he.symm))

/-- The left inclusion uses the literal scalar-extension coordinate map. -/
@[reassoc] theorem leftPulledIso_inclusion (I : Ideal (A ⊗[k] B))
    (e : Spec (CommRingCat.of ((A ⊗[k] B) ⧸ I)) ≅ D)
    (he : e.hom ≫ a = leftSupportMap k A B I) :
    (leftPulledIso k A B C a I e he).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
        (tripleIso k A B C).hom := by
  simp only [leftPulledIso, Iso.trans_hom, Category.assoc, asIso_hom,
    pullback.map, pullback.lift_fst, Category.comp_id, leftPulledSupportIso_fst]

/-- The right inclusion uses the literal right-action scalar-extension coordinate map. -/
@[reassoc] theorem rightPulledIso_inclusion (J : Ideal (B ⊗[k] C))
    (e : Spec (CommRingCat.of ((B ⊗[k] C) ⧸ J)) ≅ E)
    (he : e.hom ≫ b = rightSupportMap k B C J) :
    letI : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
      (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
    (rightPulledIso k A B C b J e he).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
        (tripleIso k A B C).hom := by
  simp only [rightPulledIso, Iso.trans_hom, Category.assoc, asIso_hom,
    pullback.map, pullback.lift_fst, Category.comp_id, rightPulledSupportIso_fst]

end Motivic.AffineMiddle.ClosedSupport
