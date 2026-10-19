/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Products.Diagonal.TripleAmbient
public import Motivic.Aglib.AlgebraicGeometry.Diagonal.Smooth
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.Kernel
public import Motivic.Aglib.AlgebraicGeometry.IdealSheaf.StalkKernel
public import Motivic.Aglib.AlgebraicGeometry.IdealSheaf.StalkPullback

/-!
# Ideals of triple diagonals
-/

@[expose] public noncomputable section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Products
open _root_.AlgebraicGeometry.Scheme.Hom

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

/-- The two Y coordinates in the original six-factor ambient. -/
abbrev correspondenceSixfoldFirstMiddlePair : correspondenceSixfoldAmbient f g h i ⟶
    pullback g g :=
  pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) ≫
    correspondenceMiddlePair f g h

/-- The first six-factor diagonal is the actual exterior base change of the
original four-factor diagonal. -/
theorem correspondenceFirstDiagonal_baseChange :
    IsPullback
      (pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h))
      (correspondenceFirstDiagonalInclusion f g h i)
      (correspondenceTripleInclusion f g h)
      (pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h)) := by
  apply IsPullback.flip
  apply IsPullback.of_right (t := (IsPullback.of_hasPullback
    (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h)).flip)
  · simpa [correspondenceAmbientTarget, correspondenceTripleTarget] using
      (IsPullback.of_hasPullback
        (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h)).flip
  · exact correspondenceFirstDiagonalInclusion_fst f g h i

/-- The actual first middle diagonal square in the six-factor ambient. -/
theorem correspondenceSixfoldFirstDiagonal_isPullback :
    IsPullback
      (pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h) ≫
        correspondenceTripleMiddle f g h)
      (correspondenceFirstDiagonalInclusion f g h i)
      (pullback.diagonal g) (correspondenceSixfoldFirstMiddlePair f g h i) :=
  (correspondenceFirstDiagonal_baseChange f g h i).paste_horiz
    (correspondenceTriple_isPullback f g h)

/-- The two Z coordinates in the same original six-factor ambient. -/
def correspondenceSixfoldSecondMiddlePair : correspondenceSixfoldAmbient f g h i ⟶
    pullback h h :=
  pullback.map _ _ h h (correspondenceAmbientTarget f g h) (pullback.fst h i) (𝟙 S)
    (by simp) (by simp)

/-- Imposing only the second middle diagonal in the original ambient. -/
abbrev correspondenceSecondDiagonalAmbient : Scheme.{u} :=
  pullback (correspondenceAmbientTarget f g h) (pullback.fst h i)

/-- The original ambient inclusion imposing only the second middle diagonal. -/
abbrev correspondenceSecondAmbientInclusion : correspondenceSecondDiagonalAmbient f g h i ⟶
    correspondenceSixfoldAmbient f g h i :=
  pullback.mapDesc (correspondenceAmbientTarget f g h) (pullback.fst h i) h

instance [IsSeparated h] : IsClosedImmersion (correspondenceSecondAmbientInclusion f g h i) :=
  inferInstanceAs (IsClosedImmersion
    (pullback.mapDesc (correspondenceAmbientTarget f g h) (pullback.fst h i) h))

/-- The second six-factor diagonal is the genuine pullback of the Z diagonal. -/
theorem correspondenceSixfoldSecondDiagonal_isPullback :
    IsPullback
      (pullback.fst (correspondenceAmbientTarget f g h) (pullback.fst h i) ≫
        correspondenceAmbientTarget f g h)
      (correspondenceSecondAmbientInclusion f g h i)
      (pullback.diagonal h) (correspondenceSixfoldSecondMiddlePair f g h i) :=
  pullback_map_diagonal_isPullback (correspondenceAmbientTarget f g h) (pullback.fst h i) h

/-- The fourfold product maps to the original second-diagonal source by the
actual first middle-diagonal inclusion. -/
def correspondenceFourfoldToSecondAmbient : correspondenceFourfoldProduct f g h i ⟶
    correspondenceSecondDiagonalAmbient f g h i :=
  pullback.map _ _ _ _ (correspondenceTripleInclusion f g h) (𝟙 _) (𝟙 Z)
    (by simp [correspondenceTripleTarget, correspondenceAmbientTarget]) (by simp)

/-- The first-pair coordinate of the fourfold-to-second-diagonal map. -/
@[reassoc (attr := simp)] theorem correspondenceFourfoldToSecondAmbient_fst :
    correspondenceFourfoldToSecondAmbient f g h i ≫
      pullback.fst (correspondenceAmbientTarget f g h) (pullback.fst h i) =
    pullback.fst (correspondenceTripleTarget f g h) (pullback.fst h i) ≫
      correspondenceTripleInclusion f g h := pullback.lift_fst _ _ _

/-- The final adjacent-product coordinate is unchanged. -/
@[reassoc (attr := simp)] theorem correspondenceFourfoldToSecondAmbient_snd :
    correspondenceFourfoldToSecondAmbient f g h i ≫
      pullback.snd (correspondenceAmbientTarget f g h) (pullback.fst h i) =
    pullback.snd (correspondenceTripleTarget f g h) (pullback.fst h i) := by
  simp only [correspondenceFourfoldToSecondAmbient, pullback.map, pullback.lift_snd,
    Category.comp_id]

/-- The second ambient diagonal keeps the first ambient coordinate. -/
@[reassoc (attr := simp)] theorem correspondenceSecondAmbientInclusion_fst :
    correspondenceSecondAmbientInclusion f g h i ≫
      pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.fst (correspondenceAmbientTarget f g h) (pullback.fst h i) := by
  simp only [correspondenceSecondAmbientInclusion, pullback.mapDesc, pullback.map,
    pullback.lift_fst, Category.comp_id]

/-- The second ambient diagonal keeps the last adjacent-product coordinate. -/
@[reassoc (attr := simp)] theorem correspondenceSecondAmbientInclusion_snd :
    correspondenceSecondAmbientInclusion f g h i ≫
      pullback.snd (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.snd (correspondenceAmbientTarget f g h) (pullback.fst h i) := by
  simp only [correspondenceSecondAmbientInclusion, pullback.mapDesc, pullback.map,
    pullback.lift_snd, Category.comp_id]

/-- The two diagonal orders define the same actual six-factor morphism. -/
@[reassoc] theorem correspondenceFourfold_diagonals_comm :
    correspondenceSecondDiagonalInclusion f g h i ≫
      correspondenceFirstDiagonalInclusion f g h i =
    correspondenceFourfoldToSecondAmbient f g h i ≫
      correspondenceSecondAmbientInclusion f g h i := by
  apply pullback.hom_ext <;> simp

/-- The second-diagonal base change still uses the original first middle inclusion. -/
theorem correspondenceFourfold_secondBaseChange :
    IsPullback
      (pullback.fst (correspondenceTripleTarget f g h) (pullback.fst h i))
      (correspondenceFourfoldToSecondAmbient f g h i)
      (correspondenceTripleInclusion f g h)
      (pullback.fst (correspondenceAmbientTarget f g h) (pullback.fst h i)) := by
  apply IsPullback.flip
  apply IsPullback.of_right (t := (IsPullback.of_hasPullback
    (correspondenceAmbientTarget f g h) (pullback.fst h i)).flip)
  · simpa [correspondenceAmbientTarget, correspondenceTripleTarget] using
      (IsPullback.of_hasPullback (correspondenceTripleTarget f g h) (pullback.fst h i)).flip
  · exact correspondenceFourfoldToSecondAmbient_fst f g h i

/-- The fourfold product is the actual Cartesian intersection of the two
middle diagonals in the original six-factor ambient. -/
theorem correspondenceFourfold_diagonals_isPullback :
    IsPullback (correspondenceSecondDiagonalInclusion f g h i)
      (correspondenceFourfoldToSecondAmbient f g h i)
      (correspondenceFirstDiagonalInclusion f g h i)
      (correspondenceSecondAmbientInclusion f g h i) := by
  apply IsPullback.of_right (t := correspondenceFirstDiagonal_baseChange f g h i)
  · simpa only [correspondenceSecondDiagonalInclusion_fst,
      correspondenceSecondAmbientInclusion_fst] using
        correspondenceFourfold_secondBaseChange f g h i
  · exact correspondenceFourfold_diagonals_comm f g h i

/-- The first ideal is literally the pullback of the Y-diagonal ideal. -/
theorem ker_correspondenceFirstDiagonal [IsSeparated g] :
    (correspondenceFirstDiagonalInclusion f g h i).ker =
      (pullback.diagonal g).ker.comap (correspondenceSixfoldFirstMiddlePair f g h i) :=
  ker_eq_comap_of_isPullback _ _ _ _ (correspondenceSixfoldFirstDiagonal_isPullback f g h i).flip

/-- The second ideal is literally the pullback of the Z-diagonal ideal. -/
theorem ker_correspondenceSecondDiagonal [IsSeparated h] :
    (correspondenceSecondAmbientInclusion f g h i).ker =
      (pullback.diagonal h).ker.comap (correspondenceSixfoldSecondMiddlePair f g h i) :=
  ker_eq_comap_of_isPullback _ _ _ _ (correspondenceSixfoldSecondDiagonal_isPullback f g h i).flip

/-- The full fourfold diagonal kernel is the sum of both actual middle ideals. -/
theorem ker_correspondenceFourfoldDiagonal [IsSeparated g] [IsSeparated h] :
    (correspondenceSecondDiagonalInclusion f g h i ≫
      correspondenceFirstDiagonalInclusion f g h i).ker =
      (correspondenceFirstDiagonalInclusion f g h i).ker ⊔
        (correspondenceSecondAmbientInclusion f g h i).ker :=
  ker_comp_eq_sup_of_isPullback _ _ _ _ (correspondenceFourfold_diagonals_isPullback f g h i)

private theorem exists_regular_diagonalIdeal_stalk {S Y : Scheme.{u}}
    (g : Y ⟶ S) [Smooth g] [IsSeparated g] (y : Y) (p : (pullback g g : Scheme.{u}))
    (hp : pullback.diagonal g y = p) :
    ∃ rs : List ((pullback g g).presheaf.stalk p),
      RingTheory.Sequence.IsRegular ((pullback g g).presheaf.stalk p) rs ∧
        (pullback.diagonal g).ker.stalk p = Ideal.ofList rs := by
  subst p
  obtain ⟨rs, hrs, hker⟩ := Diagonal.exists_regular_kernel_of_smooth g y
  exact ⟨rs, hrs, ((pullback.diagonal g).ker_stalk y).trans hker⟩

set_option backward.isDefEq.respectTransparency false in
/-- One pair of actual smooth-middle diagonal lists generates both ideals in
the same six-factor stalk after the literal two middle-coordinate stalk maps.
The lists are chosen on the middle self-products, not independently on
intermediate incidence charts. No flatness of coefficient supports is used. -/
theorem exists_common_middle_diagonalLists [Smooth g] [IsSeparated g]
    [Smooth h] [IsSeparated h] (q : correspondenceFourfoldProduct f g h i) :
    let p := (correspondenceSecondDiagonalInclusion f g h i ≫
      correspondenceFirstDiagonalInclusion f g h i) q
    ∃ (t : List ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)))
      (s : List ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p))),
      RingTheory.Sequence.IsRegular ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)) t ∧
      RingTheory.Sequence.IsRegular ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p)) s ∧
      (correspondenceFirstDiagonalInclusion f g h i).ker.stalk p =
        Ideal.ofList (t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom) ∧
      (correspondenceSecondAmbientInclusion f g h i).ker.stalk p =
        Ideal.ofList (s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom) := by
  dsimp only
  let y := correspondenceSecondDiagonalInclusion f g h i q
  let z := correspondenceFourfoldToSecondAmbient f g h i q
  have hy := congrArg (fun m => m y) (correspondenceSixfoldFirstDiagonal_isPullback f g h i).w
  have hz := congrArg (fun m => m z) (correspondenceSixfoldSecondDiagonal_isPullback f g h i).w
  have he := congrArg (fun m => m q) (correspondenceFourfold_diagonals_comm f g h i)
  change correspondenceFirstDiagonalInclusion f g h i y =
    correspondenceSecondAmbientInclusion f g h i z at he
  change pullback.diagonal h
      ((pullback.fst (correspondenceAmbientTarget f g h) (pullback.fst h i) ≫
        correspondenceAmbientTarget f g h) z) =
    correspondenceSixfoldSecondMiddlePair f g h i
      (correspondenceSecondAmbientInclusion f g h i z) at hz
  rw [← he] at hz
  change pullback.diagonal g
      ((pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h) ≫
        correspondenceTripleMiddle f g h) y) =
    correspondenceSixfoldFirstMiddlePair f g h i
      ((correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceFirstDiagonalInclusion f g h i) q) at hy
  change pullback.diagonal h
      ((pullback.fst (correspondenceAmbientTarget f g h) (pullback.fst h i) ≫
        correspondenceAmbientTarget f g h) z) =
    correspondenceSixfoldSecondMiddlePair f g h i
      ((correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceFirstDiagonalInclusion f g h i) q) at hz
  obtain ⟨t, ht, hyt⟩ := exists_regular_diagonalIdeal_stalk g _ _ hy
  obtain ⟨s, hs, hzs⟩ := exists_regular_diagonalIdeal_stalk h _ _ hz
  refine ⟨t, s, ht, hs, ?_, ?_⟩
  · rw [ker_correspondenceFirstDiagonal, Scheme.IdealSheafData.stalk_comap,
      hyt, Ideal.map_ofList]
  · rw [ker_correspondenceSecondDiagonal, Scheme.IdealSheafData.stalk_comap,
      hzs, Ideal.map_ofList]


end AlgebraicGeometry.Scheme.Products
