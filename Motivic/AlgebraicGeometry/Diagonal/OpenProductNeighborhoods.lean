/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.IntersectionAmbient
public import Motivic.AlgebraicGeometry.Intersection.ClosedAffineNeighborhood

/-!
# Actual product neighborhoods of the middle-diagonal geometry

Open neighborhoods of the three factors induce open neighborhoods of the
adjacent products, four-factor ambient space, and triple product. Their
literal middle-diagonal square commutes. Range and point-lifting statements
retain actual scheme points and do not replace product stalks by tensors.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.OpenProductNeighborhoods

variable {S X Y Z X' Y' Z' : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (uX : X' ⟶ X) (uY : Y' ⟶ Y) (uZ : Z' ⟶ Z)

/-- The actual adjacent-product map induced by two factor neighborhoods. -/
def productMap : pullback (uX ≫ f) (uY ≫ g) ⟶ pullback f g :=
  pullback.map _ _ _ _ uX uY (𝟙 S) (by simp) (by simp)

instance [IsOpenImmersion uX] [IsOpenImmersion uY] :
    IsOpenImmersion (productMap f g uX uY) :=
  inferInstanceAs (IsOpenImmersion (pullback.map _ _ _ _ uX uY (𝟙 S) (by simp) (by simp)))

/-- The first adjacent coordinate is the original first neighborhood map. -/
@[reassoc (attr := simp)] theorem productMap_fst :
    productMap f g uX uY ≫ pullback.fst f g =
      pullback.fst (uX ≫ f) (uY ≫ g) ≫ uX := pullback.lift_fst _ _ _

/-- The second adjacent coordinate is the original second neighborhood map. -/
@[reassoc (attr := simp)] theorem productMap_snd :
    productMap f g uX uY ≫ pullback.snd f g =
      pullback.snd (uX ≫ f) (uY ≫ g) ≫ uY := pullback.lift_snd _ _ _

/-- An adjacent rectangle has precisely the intersection of its coordinate ranges. -/
theorem range_productMap :
    Set.range (productMap f g uX uY) =
      pullback.fst f g ⁻¹' Set.range uX ∩ pullback.snd f g ⁻¹' Set.range uY := by
  unfold productMap
  apply Scheme.Pullback.range_map

/-- The actual ambient four-factor neighborhood uses the two adjacent rectangles. -/
def ambientMap : correspondenceIntersectionAmbient (uX ≫ f) (uY ≫ g) (uZ ≫ h) ⟶
    correspondenceIntersectionAmbient f g h :=
  pullback.map _ _ _ _ (productMap f g uX uY) (productMap g h uY uZ) (𝟙 S)
    (by simp) (by simp)

instance [IsOpenImmersion uX] [IsOpenImmersion uY] [IsOpenImmersion uZ] :
    IsOpenImmersion (ambientMap f g h uX uY uZ) :=
  inferInstanceAs (IsOpenImmersion
    (pullback.map _ _ _ _ (productMap f g uX uY) (productMap g h uY uZ) (𝟙 S) (by simp) (by simp)))

/-- The triple-product neighborhood identifies the same middle open coordinate. -/
def tripleMap : correspondenceTripleProduct (uX ≫ f) (uY ≫ g) (uZ ≫ h) ⟶
    correspondenceTripleProduct f g h :=
  pullback.map _ _ _ _ (productMap f g uX uY) (productMap g h uY uZ) uY
    (by simp) (by simp)

instance [IsOpenImmersion uX] [IsOpenImmersion uY] [IsOpenImmersion uZ] :
    IsOpenImmersion (tripleMap f g h uX uY uZ) :=
  inferInstanceAs (IsOpenImmersion
    (pullback.map _ _ _ _ (productMap f g uX uY) (productMap g h uY uZ) uY (by simp) (by simp)))

/-- The ambient neighborhood retains the actual first adjacent projection. -/
@[reassoc (attr := simp)] theorem ambientMap_fst :
    ambientMap f g h uX uY uZ ≫ pullback.fst (pullback.snd f g ≫ g)
      (pullback.fst g h ≫ g) =
    pullback.fst (pullback.snd (uX ≫ f) (uY ≫ g) ≫ uY ≫ g)
      (pullback.fst (uY ≫ g) (uZ ≫ h) ≫ uY ≫ g) ≫ productMap f g uX uY :=
  pullback.lift_fst _ _ _

/-- The ambient neighborhood retains the actual second adjacent projection. -/
@[reassoc (attr := simp)] theorem ambientMap_snd :
    ambientMap f g h uX uY uZ ≫ pullback.snd (pullback.snd f g ≫ g)
      (pullback.fst g h ≫ g) =
    pullback.snd (pullback.snd (uX ≫ f) (uY ≫ g) ≫ uY ≫ g)
      (pullback.fst (uY ≫ g) (uZ ≫ h) ≫ uY ≫ g) ≫ productMap g h uY uZ :=
  pullback.lift_snd _ _ _

/-- The triple neighborhood retains the actual first adjacent projection. -/
@[reassoc (attr := simp)] theorem tripleMap_fst :
    tripleMap f g h uX uY uZ ≫ pullback.fst (pullback.snd f g) (pullback.fst g h) =
    pullback.fst (pullback.snd (uX ≫ f) (uY ≫ g))
      (pullback.fst (uY ≫ g) (uZ ≫ h)) ≫ productMap f g uX uY :=
  pullback.lift_fst _ _ _

/-- The triple neighborhood retains the actual second adjacent projection. -/
@[reassoc (attr := simp)] theorem tripleMap_snd :
    tripleMap f g h uX uY uZ ≫ pullback.snd (pullback.snd f g) (pullback.fst g h) =
    pullback.snd (pullback.snd (uX ≫ f) (uY ≫ g))
      (pullback.fst (uY ≫ g) (uZ ≫ h)) ≫ productMap g h uY uZ :=
  pullback.lift_snd _ _ _

/-- The genuine middle-diagonal inclusion commutes with the product neighborhoods. -/
@[reassoc] theorem tripleMap_inclusion :
    tripleMap f g h uX uY uZ ≫ correspondenceTripleInclusion f g h =
      correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) ≫
        ambientMap f g h uX uY uZ := by
  apply pullback.hom_ext <;> simp

/-- The range in the triple product is determined by its two adjacent rectangles. -/
theorem range_tripleMap [IsOpenImmersion uY] :
    Set.range (tripleMap f g h uX uY uZ) =
      pullback.fst (pullback.snd f g) (pullback.fst g h) ⁻¹'
        Set.range (productMap f g uX uY) ∩
      pullback.snd (pullback.snd f g) (pullback.fst g h) ⁻¹'
        Set.range (productMap g h uY uZ) := by
  unfold tripleMap
  apply Scheme.Pullback.range_map

/-- Any actual triple point lies in a triple neighborhood with affine factor
schemes. All factor charts and the triple point lift are constructed. -/
theorem exists_affineTripleNeighborhood (w : correspondenceTripleProduct f g h) :
    ∃ A B C : CommRingCat.{u},
    ∃ uX : Spec A ⟶ X, ∃ uY : Spec B ⟶ Y, ∃ uZ : Spec C ⟶ Z,
      IsOpenImmersion uX ∧ IsOpenImmersion uY ∧ IsOpenImmersion uZ ∧
      ∃ q : correspondenceTripleProduct (uX ≫ f) (uY ≫ g) (uZ ≫ h),
        tripleMap f g h uX uY uZ q = w := by
  obtain ⟨A, uX, huX, x, hx⟩ := Scheme.exists_Spec_apply_eq
    (pullback.fst f g (pullback.fst (pullback.snd f g) (pullback.fst g h) w))
  obtain ⟨B, uY, huY, y, hy⟩ := Scheme.exists_Spec_apply_eq
    (pullback.snd f g (pullback.fst (pullback.snd f g) (pullback.fst g h) w))
  obtain ⟨C, uZ, huZ, z, hz⟩ := Scheme.exists_Spec_apply_eq
    (pullback.snd g h (pullback.snd (pullback.snd f g) (pullback.fst g h) w))
  let := huX
  let := huY
  let := huZ
  refine ⟨A, B, C, uX, uY, uZ, huX, huY, huZ, ?_⟩
  change w ∈ Set.range (tripleMap f g h uX uY uZ)
  rw [range_tripleMap]
  constructor
  · change pullback.fst (pullback.snd f g) (pullback.fst g h) w ∈
      Set.range (productMap f g uX uY)
    rw [range_productMap]
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · change pullback.snd (pullback.snd f g) (pullback.fst g h) w ∈
      Set.range (productMap g h uY uZ)
    rw [range_productMap]
    refine ⟨⟨y, ?_⟩, ⟨z, hz⟩⟩
    exact hy.trans (congrArg (fun m ↦ m w)
      (pullback.condition (f := pullback.snd f g) (g := pullback.fst g h)))

end Motivic.OpenProductNeighborhoods
