/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Products.Triple.Basic

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Support.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The closed incidence embedding in the triple product

The incidence scheme of two geometric finite correspondences embeds as a
closed subscheme of `(X ×[S] Y) ×[Y] (Y ×[S] Z)`. Its closed support is
exactly the intersection of the two inverse-image supports. Its actual ideal
is the sum of the pulled-back ideals, and its full scheme structure is
identified with this closed intersection. Projection from
this ambient triple product to `X ×[S] Z` recovers the incidence map.

These statements concern actual schemes and their closed supports. They do
not assign intersection multiplicities or assert proper intersection.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme.Hom _root_.AlgebraicGeometry.Scheme.Products

variable {f g h} (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

/-- The actual closed embedding of the incidence scheme in the ambient triple product. -/
noncomputable def incidenceInclusion : A.incidence B ⟶ correspondenceTripleProduct f g h :=
  pullback.map A.targetProjection B.projection (pullback.snd f g) (pullback.fst g h)
    A.inclusion B.inclusion (𝟙 Y) (by simp) (by simp [projection, correspondenceProjection])

@[reassoc (attr := simp)]
theorem incidenceInclusion_fst :
    A.incidenceInclusion B ≫ pullback.fst (pullback.snd f g) (pullback.fst g h) =
      A.incidenceFst B ≫ A.inclusion :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem incidenceInclusion_snd :
    A.incidenceInclusion B ≫ pullback.snd (pullback.snd f g) (pullback.fst g h) =
      A.incidenceSnd B ≫ B.inclusion :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
instance : IsClosedImmersion (A.incidenceInclusion B) := by
  unfold incidenceInclusion
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion A.inclusion))
    (inferInstanceAs (IsClosedImmersion B.inclusion)) rfl rfl

/-- Ambient projection restricts to the incidence scheme's actual source-target map. -/
@[reassoc (attr := simp)]
theorem incidenceInclusion_projection :
    A.incidenceInclusion B ≫ correspondenceTripleProjection f g h = A.incidenceMap B := by
  apply pullback.hom_ext <;> simp [incidenceSource, incidenceTarget,
    projection, correspondenceProjection, targetProjection]

/-- The image of the closed incidence embedding is exactly the two-support intersection. -/
theorem range_incidenceInclusion :
    Set.range (A.incidenceInclusion B) =
      pullback.fst (pullback.snd f g) (pullback.fst g h) ⁻¹' (A.val.support : Set _) ∩
        pullback.snd (pullback.snd f g) (pullback.fst g h) ⁻¹' (B.val.support : Set _) := by
  rw [incidenceInclusion, Scheme.Pullback.range_map]
  simp only [inclusion, Scheme.IdealSheafData.range_subschemeι]

/-- The scheme-theoretic incidence image has precisely that intersection as closed support. -/
theorem support_incidenceInclusion_ker :
    ((A.incidenceInclusion B).ker.support : Set (correspondenceTripleProduct f g h)) =
      pullback.fst (pullback.snd f g) (pullback.fst g h) ⁻¹' (A.val.support : Set _) ∩
        pullback.snd (pullback.snd f g) (pullback.fst g h) ⁻¹' (B.val.support : Set _) := by
  rw [support_finiteImage, A.range_incidenceInclusion B]

/-- The incidence scheme has exactly the sum of the two pulled-back ideal sheaves.
This identity retains the scheme structures, including any nilpotents. -/
theorem ker_incidenceInclusion :
    (A.incidenceInclusion B).ker =
      A.val.comap (pullback.fst (pullback.snd f g) (pullback.fst g h)) ⊔
        B.val.comap (pullback.snd (pullback.snd f g) (pullback.fst g h)) := by
  let p := pullback.fst (pullback.snd f g) (pullback.fst g h)
  let q := pullback.snd (pullback.snd f g) (pullback.fst g h)
  let I := A.val.comap p ⊔ B.val.comap q
  apply le_antisymm
  · have hA : A.inclusion.ker ≤ (I.subschemeι ≫ p).ker := by
      rw [show A.inclusion.ker = A.val from A.val.ker_subschemeι]
      exact Scheme.IdealSheafData.le_map_iff_comap_le.mpr le_sup_left
    have hB : B.inclusion.ker ≤ (I.subschemeι ≫ q).ker := by
      rw [show B.inclusion.ker = B.val from B.val.ker_subschemeι]
      exact Scheme.IdealSheafData.le_map_iff_comap_le.mpr le_sup_right
    let a := IsClosedImmersion.lift A.inclusion (I.subschemeι ≫ p) hA
    let b := IsClosedImmersion.lift B.inclusion (I.subschemeι ≫ q) hB
    have ha : a ≫ A.inclusion = I.subschemeι ≫ p := IsClosedImmersion.lift_fac _ _ _
    have hb : b ≫ B.inclusion = I.subschemeι ≫ q := IsClosedImmersion.lift_fac _ _ _
    have hab : a ≫ A.targetProjection = b ≫ B.projection := by
      change a ≫ (A.inclusion ≫ pullback.snd f g) =
        b ≫ (B.inclusion ≫ pullback.fst g h)
      rw [← Category.assoc, ha, Category.assoc, pullback.condition,
        ← Category.assoc, ← hb, Category.assoc]
    let i : I.subscheme ⟶ A.incidence B := pullback.lift a b hab
    have hi : i ≫ A.incidenceInclusion B = I.subschemeι := by
      apply pullback.hom_ext
      · simpa only [i, p, incidenceFst, Category.assoc, incidenceInclusion_fst,
          pullback.lift_fst_assoc]
          using ha
      · simpa only [i, q, incidenceSnd, Category.assoc, incidenceInclusion_snd,
          pullback.lift_snd_assoc]
          using hb
    have hk := Scheme.Hom.le_ker_comp i (A.incidenceInclusion B)
    rwa [hi, I.ker_subschemeι] at hk
  · apply sup_le
    · apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
      rw [← Scheme.Hom.ker_comp, A.incidenceInclusion_fst B]
      simpa only [inclusion, Scheme.IdealSheafData.ker_subschemeι] using
        Scheme.Hom.le_ker_comp (A.incidenceFst B) A.inclusion
    · apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
      rw [← Scheme.Hom.ker_comp, A.incidenceInclusion_snd B]
      simpa only [inclusion, Scheme.IdealSheafData.ker_subschemeι] using
        Scheme.Hom.le_ker_comp (A.incidenceSnd B) B.inclusion

/-- The genuine incidence scheme is isomorphic to the subscheme cut out by the
sum of the pulled-back ideals, with its full scheme structure. -/
noncomputable def incidenceIntersectionIso :
    A.incidence B ≅
      (A.val.comap (pullback.fst (pullback.snd f g) (pullback.fst g h)) ⊔
        B.val.comap (pullback.snd (pullback.snd f g) (pullback.fst g h))).subscheme :=
  asIso (A.incidenceInclusion B).toImage ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme (A.ker_incidenceInclusion B))

end FiniteCorrespondenceGenerator

end Motivic
