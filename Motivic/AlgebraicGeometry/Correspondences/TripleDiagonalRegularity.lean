/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleDiagonalIdeals

/-!
# Regularity of the literal common six-factor diagonal lists

The actual middle-pair maps are flat under flatness of their outer structure
maps. Hence the original common middle lists remain regular in the one actual
six-factor stalk. Properness follows from the genuine combined-diagonal
source stalk. No regularity or flatness of a support coefficient is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence

universe u

namespace Motivic

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

/-- Flat outer structure maps make the literal first middle-pair projection flat. -/
instance [Flat f] [Flat h] [Flat i] :
    Flat (correspondenceSixfoldFirstMiddlePair f g h i) := by
  unfold correspondenceSixfoldFirstMiddlePair
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The second middle-pair projection is flat for the actual flat outer factors. -/
instance [Flat f] [Flat g] [Flat i] :
    Flat (correspondenceSixfoldSecondMiddlePair f g h i) := by
  unfold correspondenceSixfoldSecondMiddlePair
  exact MorphismProperty.pullbackMap (P := @Flat)
    (inferInstanceAs (Flat (correspondenceAmbientTarget f g h)))
    (inferInstanceAs (Flat (pullback.fst h i))) rfl rfl

/-- The two literal mapped lists are regular in the same actual ambient stalk.
The full diagonal stalk supplies properness for both generated ideals. -/
theorem common_middle_diagonalLists_isRegular [Flat f] [Flat g] [Flat h] [Flat i]
    [IsSeparated g] [IsSeparated h] (q : correspondenceFourfoldProduct f g h i) :
    let d := correspondenceSecondDiagonalInclusion f g h i ≫
      correspondenceFirstDiagonalInclusion f g h i
    let p := d q
    ∀ (t : List ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)))
      (s : List ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p))),
      IsWeaklyRegular ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)) t →
      IsWeaklyRegular ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p)) s →
      (correspondenceFirstDiagonalInclusion f g h i).ker.stalk p =
        Ideal.ofList (t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom) →
      (correspondenceSecondAmbientInclusion f g h i).ker.stalk p =
        Ideal.ofList (s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom) →
      IsRegular ((correspondenceSixfoldAmbient f g h i).presheaf.stalk p)
        (t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom) ∧
      IsRegular ((correspondenceSixfoldAmbient f g h i).presheaf.stalk p)
        (s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom) := by
  dsimp only
  intro t s ht hs hyt hzs
  let d := correspondenceSecondDiagonalInclusion f g h i ≫
    correspondenceFirstDiagonalInclusion f g h i
  have hk : RingHom.ker (d.stalkMap q).hom =
      (correspondenceFirstDiagonalInclusion f g h i).ker.stalk (d q) ⊔
      (correspondenceSecondAmbientInclusion f g h i).ker.stalk (d q) := by
    rw [← d.ker_stalk q, ker_correspondenceFourfoldDiagonal,
      Scheme.IdealSheafData.stalk_sup]
  constructor
  · apply RegularSequence.isRegular_map_of_flat_of_le_ker
      ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap (d q)).hom
      (d.stalkMap q).hom (Flat.stalkMap _ _) ht
    rw [← hyt, hk]
    exact le_sup_left
  · apply RegularSequence.isRegular_map_of_flat_of_le_ker
      ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap (d q)).hom
      (d.stalkMap q).hom (Flat.stalkMap _ _) hs
    rw [← hzs, hk]
    exact le_sup_right

/-- Choose the original common middle lists once. Their literal images both
generate the correct diagonal ideals and are regular in the common ambient. -/
theorem exists_common_regular_middle_diagonalLists [Flat f] [Smooth g] [IsSeparated g]
    [Smooth h] [IsSeparated h] [Flat i] (q : correspondenceFourfoldProduct f g h i) :
    let p := (correspondenceSecondDiagonalInclusion f g h i ≫
      correspondenceFirstDiagonalInclusion f g h i) q
    ∃ (t : List ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)))
      (s : List ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p))),
      IsRegular ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)) t ∧
      IsRegular ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p)) s ∧
      IsRegular ((correspondenceSixfoldAmbient f g h i).presheaf.stalk p)
        (t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom) ∧
      IsRegular ((correspondenceSixfoldAmbient f g h i).presheaf.stalk p)
        (s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom) ∧
      (correspondenceFirstDiagonalInclusion f g h i).ker.stalk p =
        Ideal.ofList (t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom) ∧
      (correspondenceSecondAmbientInclusion f g h i).ker.stalk p =
        Ideal.ofList (s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom) := by
  obtain ⟨t, s, ht, hs, hyt, hzs⟩ := exists_common_middle_diagonalLists f g h i q
  obtain ⟨ht', hs'⟩ := common_middle_diagonalLists_isRegular f g h i q t s
    ht.toIsWeaklyRegular hs.toIsWeaklyRegular hyt hzs
  exact ⟨t, s, ht, hs, ht', hs', hyt, hzs⟩

/-- At every actual first-stage point the first diagonal has a regular stalk
kernel, obtained from the same original smooth middle diagonal by flat pullback. -/
theorem exists_regular_kernel_correspondenceFirstDiagonal [Flat f] [Smooth g]
    [IsSeparated g] [Flat h] [Flat i] (q : correspondenceFirstDiagonal f g h i) :
    ∃ t : List ((correspondenceSixfoldAmbient f g h i).presheaf.stalk
        (correspondenceFirstDiagonalInclusion f g h i q)),
      IsRegular ((correspondenceSixfoldAmbient f g h i).presheaf.stalk
        (correspondenceFirstDiagonalInclusion f g h i q)) t ∧
      RingHom.ker ((correspondenceFirstDiagonalInclusion f g h i).stalkMap q).hom =
        Ideal.ofList t :=
  Diagonal.exists_regular_kernel_of_flat_isPullback
    (correspondenceSixfoldFirstDiagonal_isPullback f g h i) q
    (Diagonal.exists_regular_kernel_of_smooth g _)

end Motivic
