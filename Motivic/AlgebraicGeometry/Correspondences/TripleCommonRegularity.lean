/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleCombinedRegularity
public import Motivic.AlgebraicGeometry.Correspondences.IntermediateDiagonalLists

/-!
# Joint regularity of the same original two middle-diagonal lists

The remaining middle-pair map after the first diagonal is flat. Its actual
stalk map is the composite of the original six-factor middle map and the first
closed-stalk surjection. Thus the same original second list is regular over
the first quotient. The literal images of the original two lists can now be
appended using the surjective-kernel theorem, with no new choice of lifts.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence

universe u

namespace Motivic

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- The original remaining middle pair restricts to the actual middle-pair
projection on the first-diagonal ambient. -/
@[reassoc]
theorem correspondenceFirstDiagonal_secondMiddlePair :
    correspondenceFirstDiagonalInclusion f g h i ≫
      correspondenceSixfoldSecondMiddlePair f g h i =
    pullback.map _ _ h h (correspondenceTripleTarget f g h) (pullback.fst h i) (𝟙 S)
      (by simp) (by simp) := by
  apply pullback.hom_ext <;>
    simp [correspondenceSixfoldSecondMiddlePair, pullback.map,
      correspondenceTripleTarget, correspondenceAmbientTarget]

/-- The remaining pair is flat after the first diagonal, for the genuine
flat outer factors. This does not assert flatness of a support coefficient. -/
instance [Flat f] [Flat g] [Flat i] :
    Flat (correspondenceFirstDiagonalInclusion f g h i ≫
      correspondenceSixfoldSecondMiddlePair f g h i) := by
  rw [correspondenceFirstDiagonal_secondMiddlePair]
  exact MorphismProperty.pullbackMap (P := @Flat)
    (inferInstanceAs (Flat (correspondenceTripleTarget f g h)))
    (inferInstanceAs (Flat (pullback.fst h i))) rfl rfl

set_option backward.isDefEq.respectTransparency false in
/-- The literal same second list generates the actual second kernel after
passing through the first closed-stalk surjection. -/
theorem common_secondList_quotient_kernel [IsSeparated h]
    (q : correspondenceFourfoldProduct f g h i)
    (s : List ((pullback h h).presheaf.stalk
      (correspondenceSixfoldSecondMiddlePair f g h i
        ((correspondenceSecondDiagonalInclusion f g h i ≫
          correspondenceFirstDiagonalInclusion f g h i) q))))
    (hks : (correspondenceSecondAmbientInclusion f g h i).ker.stalk
        ((correspondenceSecondDiagonalInclusion f g h i ≫
          correspondenceFirstDiagonalInclusion f g h i) q) =
      Ideal.ofList (s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
        ((correspondenceSecondDiagonalInclusion f g h i ≫
          correspondenceFirstDiagonalInclusion f g h i) q)).hom)) :
    RingHom.ker ((correspondenceSecondDiagonalInclusion f g h i).stalkMap q).hom =
      Ideal.ofList ((s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
        ((correspondenceSecondDiagonalInclusion f g h i ≫
          correspondenceFirstDiagonalInclusion f g h i) q)).hom).map
        ((correspondenceFirstDiagonalInclusion f g h i).stalkMap
          (correspondenceSecondDiagonalInclusion f g h i q)).hom) := by
  rw [← (correspondenceSecondDiagonalInclusion f g h i).ker_stalk q,
    ker_eq_comap_of_isPullback _ _ _ _
      (correspondenceFourfold_diagonals_isPullback f g h i),
    Scheme.IdealSheafData.stalk_comap]
  exact (congrArg (fun J => J.map
    ((correspondenceFirstDiagonalInclusion f g h i).stalkMap
      (correspondenceSecondDiagonalInclusion f g h i q)).hom) hks).trans
    (Ideal.map_ofList _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The same original second list is genuinely regular in the first quotient,
using the flat remaining-middle map and the actual final nonzero stalk. -/
theorem common_secondList_isRegular_quotient [Flat f] [Flat g] [Flat i]
    [IsSeparated h] (q : correspondenceFourfoldProduct f g h i)
    (s : List ((pullback h h).presheaf.stalk
      (correspondenceSixfoldSecondMiddlePair f g h i
        ((correspondenceSecondDiagonalInclusion f g h i ≫
          correspondenceFirstDiagonalInclusion f g h i) q))))
    (hs : IsWeaklyRegular ((pullback h h).presheaf.stalk
      (correspondenceSixfoldSecondMiddlePair f g h i
        ((correspondenceSecondDiagonalInclusion f g h i ≫
          correspondenceFirstDiagonalInclusion f g h i) q))) s)
    (hks : (correspondenceSecondAmbientInclusion f g h i).ker.stalk
        ((correspondenceSecondDiagonalInclusion f g h i ≫
          correspondenceFirstDiagonalInclusion f g h i) q) =
      Ideal.ofList (s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
        ((correspondenceSecondDiagonalInclusion f g h i ≫
          correspondenceFirstDiagonalInclusion f g h i) q)).hom)) :
    IsRegular ((correspondenceFirstDiagonal f g h i).presheaf.stalk
      (correspondenceSecondDiagonalInclusion f g h i q))
      ((s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
        ((correspondenceSecondDiagonalInclusion f g h i ≫
          correspondenceFirstDiagonalInclusion f g h i) q)).hom).map
        ((correspondenceFirstDiagonalInclusion f g h i).stalkMap
          (correspondenceSecondDiagonalInclusion f g h i q)).hom) := by
  let a := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
    ((correspondenceSecondDiagonalInclusion f g h i ≫
      correspondenceFirstDiagonalInclusion f g h i) q)).hom
  let b := ((correspondenceFirstDiagonalInclusion f g h i).stalkMap
    (correspondenceSecondDiagonalInclusion f g h i q)).hom
  let c := ((correspondenceSecondDiagonalInclusion f g h i).stalkMap q).hom
  have hab : (b.comp a).Flat := by
    have hh := Flat.stalkMap (correspondenceFirstDiagonalInclusion f g h i ≫
      correspondenceSixfoldSecondMiddlePair f g h i)
        (correspondenceSecondDiagonalInclusion f g h i q)
    rw [Scheme.Hom.stalkMap_comp] at hh
    exact hh
  have hk : RingHom.ker c = Ideal.ofList ((s.map a).map b) :=
    common_secondList_quotient_kernel f g h i q s hks
  have heq : (s.map a).map b = s.map (b.comp a) := by
    rw [List.map_map]
    rfl
  have hle : Ideal.ofList (s.map (b.comp a)) ≤ RingHom.ker c := by
    rw [← heq]
    exact hk.ge
  have hreg := RegularSequence.isRegular_map_of_flat_of_le_ker (b.comp a) c hab hs hle
  rw [← heq] at hreg
  exact hreg

set_option backward.isDefEq.respectTransparency false in
/-- The literal images of the original two common middle lists form a regular
append generating the genuine combined two-diagonal kernel. -/
theorem common_middle_diagonalLists_append_regular [Flat f] [Flat g] [Flat h] [Flat i]
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
      let r := t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom ++
        s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
      IsRegular ((correspondenceSixfoldAmbient f g h i).presheaf.stalk p) r ∧
        RingHom.ker (d.stalkMap q).hom = Ideal.ofList r := by
  dsimp only
  intro t s ht hs hkt hks
  have hfirst := (common_middle_diagonalLists_isRegular f g h i q t s ht hs hkt hks).1
  have hkfirst : RingHom.ker
      ((correspondenceFirstDiagonalInclusion f g h i).stalkMap
        (correspondenceSecondDiagonalInclusion f g h i q)).hom =
      Ideal.ofList (t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap
        ((correspondenceSecondDiagonalInclusion f g h i ≫
          correspondenceFirstDiagonalInclusion f g h i) q)).hom) := by
    rw [← (correspondenceFirstDiagonalInclusion f g h i).ker_stalk]
    exact hkt
  obtain ⟨hr, hker⟩ := RegularSequence.isRegular_append_of_surjective_kernel
    ((correspondenceFirstDiagonalInclusion f g h i).stalkMap
      (correspondenceSecondDiagonalInclusion f g h i q)).hom
    ((correspondenceSecondDiagonalInclusion f g h i).stalkMap q).hom
    ((correspondenceFirstDiagonalInclusion f g h i).stalkMap_surjective _)
    _ _ hfirst hkfirst
    (common_secondList_isRegular_quotient f g h i q s hs hks)
    (common_secondList_quotient_kernel f g h i q s hks)
  refine ⟨hr, ?_⟩
  rw [Scheme.Hom.stalkMap_comp]
  exact hker

end Motivic
