/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtalePointOpenRefinement
public import Motivic.Aglib.AlgebraicGeometry.ClosedFiberEtaleEqualization
public import Mathlib.CategoryTheory.Filtered.Final

/-! # Marked neighborhoods of a split closed subscheme

The functor is literal base change on the existing full field-valued
neighborhood categories. A retraction extends objects; closed-fiber etale
equalization supplies ambient refinements of parallel arrows.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite

variable {Z Y : Scheme.{u}} (i : Z ⟶ Y) (K : Type u) [Field K]
  (c : Spec (.of K) ⟶ Z)

/-- The original marked point on the actual closed fiber of a neighborhood. -/
def closedNeighborhoodMark (N : FieldValuedNeighborhood (c ≫ i) K (𝟙 _)) :
    Over.mk (𝟙 _ ≫ c) ⟶
      (MorphismProperty.Over.forget _ _ Z).obj ((baseChange i).obj N.obj) :=
  Over.homMk (pullback.lift N.val.left c (by simp))
    (by
      change pullback.lift N.val.left c _ ≫ pullback.snd N.obj.hom i = 𝟙 _ ≫ c
      simp only [pullback.lift_snd, Category.id_comp])

/-- Literal pullback on full-marked neighborhoods, retaining the coefficient field. -/
def closedNeighborhoodBaseChange :
    FieldValuedNeighborhood (c ≫ i) K (𝟙 _) ⥤
      FieldValuedNeighborhood c K (𝟙 _) where
  obj N := Functor.elementsMk _ ((baseChange i).obj N.obj)
    (closedNeighborhoodMark i K c N)
  map {N M} a := Functor.Elements.homMk ((baseChange i).map a.hom) (by
    apply Over.OverMorphism.ext
    change (pullback.lift N.val.left c _) ≫ ((baseChange i).map a.hom).left =
      pullback.lift M.val.left c _
    apply pullback.hom_ext
    · have hf : ((baseChange i).map a.hom).left ≫ pullback.fst M.obj.hom i =
          pullback.fst N.obj.hom i ≫ a.hom.left := pullback.lift_fst _ _ _
      simp only [Category.assoc, hf, pullback.lift_fst_assoc, pullback.lift_fst]
      exact congrArg (fun t => t.left) a.map_val
    · have hs : ((baseChange i).map a.hom).left ≫ pullback.snd M.obj.hom i =
          pullback.snd N.obj.hom i := pullback.lift_snd _ _ _
      erw [Category.assoc, hs, pullback.lift_snd, pullback.lift_snd])
  map_id _ := by apply Functor.Elements.hom_ext; exact (baseChange i).map_id _
  map_comp _ _ := by apply Functor.Elements.hom_ext; exact (baseChange i).map_comp _ _

/-- A retraction extends every marked etale neighborhood on the closed scheme.
Only an arrow from the original closed base change is needed for initiality. -/
theorem closedNeighborhoodBaseChange_exists_lift
    (p : Y ⟶ Z) (hip : i ≫ p = 𝟙 Z)
    (N : FieldValuedNeighborhood c K (𝟙 _)) :
    ∃ M : FieldValuedNeighborhood (c ≫ i) K (𝟙 _),
      Nonempty ((closedNeighborhoodBaseChange i K c).obj M ⟶ N) := by
  let W := (baseChange p).obj N.obj
  let a : Spec (.of K) ⟶ W.left := pullback.lift N.val.left (c ≫ i) (by
    rw [Category.assoc, hip, Category.comp_id]
    simp)
  let m : Over.mk (𝟙 _ ≫ (c ≫ i)) ⟶
      (MorphismProperty.Over.forget _ _ Y).obj W :=
    Over.homMk a (by
      change pullback.lift N.val.left (c ≫ i) _ ≫ pullback.snd N.obj.hom p = 𝟙 _ ≫ (c ≫ i)
      simp only [pullback.lift_snd, Category.id_comp])
  let M : FieldValuedNeighborhood (c ≫ i) K (𝟙 _) := Functor.elementsMk _ W m
  let f : (baseChange i).obj W ⟶ N.obj :=
    MorphismProperty.Over.homMk
      (pullback.fst W.hom i ≫ pullback.fst N.obj.hom p) (by
        change (pullback.fst W.hom i ≫ pullback.fst N.obj.hom p) ≫ N.obj.hom =
          pullback.snd W.hom i
        have hw : W.hom = pullback.snd N.obj.hom p := rfl
        erw [Category.assoc, pullback.condition, ← hw, ← Category.assoc,
          pullback.condition, Category.assoc, hip, Category.comp_id])
  refine ⟨M, ⟨Functor.Elements.homMk f ?_⟩⟩
  apply Over.OverMorphism.ext
  change (pullback.lift m.left c _) ≫
    (pullback.fst W.hom i ≫ pullback.fst N.obj.hom p) = N.val.left
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ pullback.fst N.obj.hom p)
      (pullback.lift_fst m.left c _)).trans (pullback.lift_fst _ _ _))

/-- Parallel arrows on the closed fiber become equal on the closed fiber of an
actual ambient open containing the unchanged full marking. -/
theorem closedNeighborhoodBaseChange_equalizes [IsClosedImmersion i]
    {N : FieldValuedNeighborhood c K (𝟙 _)}
    {M : FieldValuedNeighborhood (c ≫ i) K (𝟙 _)} [IsNoetherian M.obj.left]
    (f g : (closedNeighborhoodBaseChange i K c).obj M ⟶ N) :
    ∃ (M' : FieldValuedNeighborhood (c ≫ i) K (𝟙 _)) (t : M' ⟶ M),
      (closedNeighborhoodBaseChange i K c).map t ≫ f =
        (closedNeighborhoodBaseChange i K c).map t ≫ g := by
  let D := (baseChange i).obj M.obj
  let a := (closedNeighborhoodMark i K c M).left
  let f' := (MorphismProperty.Over.forget _ _ Z).map f.hom
  let g' := (MorphismProperty.Over.forget _ _ Z).map g.hom
  have ha : a ≫ f'.left = a ≫ g'.left := by
    have hf := congrArg (fun t => t.left) f.map_val
    have hg := congrArg (fun t => t.left) g.map_val
    change a ≫ f'.left = N.val.left at hf
    change a ≫ g'.left = N.val.left at hg
    exact hf.trans hg.symm
  let : Etale ((MorphismProperty.Over.forget _ _ Z).obj N.obj).hom :=
    inferInstanceAs (Etale N.obj.hom)
  obtain ⟨O, hmark, heq⟩ := Scheme.Hom.exists_open_closedFiber_equalizes
    (pullback.fst M.obj.hom i) f' g' a ha
  have hmark' : Set.range M.val.left ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    rintro y ⟨t, rfl⟩
    have hm : a ≫ pullback.fst M.obj.hom i = M.val.left := pullback.lift_fst _ _ _
    exact hmark ⟨t, congrArg (fun q : Spec (.of K) ⟶ M.obj.left => q t) hm⟩
  let l := IsOpenImmersion.lift O.ι M.val.left hmark'
  have hl : l ≫ O.ι = M.val.left := IsOpenImmersion.lift_fac _ _ _
  let W := testOpenObject M.obj O
  let m : Over.mk (𝟙 _ ≫ (c ≫ i)) ⟶
      (MorphismProperty.Over.forget _ _ Y).obj W := Over.homMk l (by
        change l ≫ (O.ι ≫ M.obj.hom) = _
        exact (Category.assoc l O.ι M.obj.hom).symm.trans
          ((congrArg (fun t => t ≫ M.obj.hom) hl).trans (Over.w M.val)))
  let M' : FieldValuedNeighborhood (c ≫ i) K (𝟙 _) := Functor.elementsMk _ W m
  let t : M' ⟶ M := Functor.Elements.homMk (testOpenInclusion M.obj O) (by
    apply Over.OverMorphism.ext
    exact hl)
  let b := ((baseChange i).map (testOpenInclusion M.obj O)).left
  have hb : b ≫ pullback.fst M.obj.hom i = pullback.fst W.hom i ≫ O.ι :=
    pullback.lift_fst _ _ _
  let d := pullback.lift b (pullback.fst W.hom i) hb
  have hd : d ≫ pullback.fst (pullback.fst M.obj.hom i) O.ι = b :=
    pullback.lift_fst _ _ _
  refine ⟨M', t, ?_⟩
  apply Functor.Elements.hom_ext
  apply MorphismProperty.Over.Hom.ext
  change b ≫ f'.left = b ≫ g'.left
  rw [← hd, Category.assoc, Category.assoc, heq]

/-- On a split closed immersion, literal closed base change is initial on the
original full field-valued marked-neighborhood categories. -/
theorem closedNeighborhoodBaseChange_initial [IsClosedImmersion i] [IsNoetherian Y]
    (p : Y ⟶ Z) (hip : i ≫ p = 𝟙 Z) :
    (closedNeighborhoodBaseChange i K c).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered
  · exact closedNeighborhoodBaseChange_exists_lift i K c p hip
  · intro N M f g
    let : CompactSpace M.obj.left :=
      QuasiCompact.compactSpace_of_compactSpace (show M.obj.left ⟶ Y from M.obj.hom)
    let : IsLocallyNoetherian M.obj.left :=
      LocallyOfFiniteType.isLocallyNoetherian (show M.obj.left ⟶ Y from M.obj.hom)
    let : IsNoetherian M.obj.left := ⟨⟩
    exact closedNeighborhoodBaseChange_equalizes i K c f g

end Motivic.FiniteEtaleSite
