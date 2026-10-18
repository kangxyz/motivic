/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteBaseChange
public import Motivic.AlgebraicGeometry.SmoothSiteNisnevichPullbacks

/-! # Native scalar lifts into the original étale pullback

The map is constructed from the two actual scheme pullback universal properties.
Both original projections are retained; no scalar comparison is supplied as data.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.SmoothSite

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {X Y Z : SmoothSite (Spec (.of k))} (f : X ⟶ Z) (g : Y ⟶ Z) [Etale f.left]
  {Q : SmoothSite (Spec (.of L))}
  (a : Q ⟶ (fieldBaseChange (algebraMap k L)).obj X)
  (b : Q ⟶ (fieldBaseChange (algebraMap k L)).obj Y)
  (h : a ≫ (fieldBaseChange (algebraMap k L)).map f =
    b ≫ (fieldBaseChange (algebraMap k L)).map g)

/-- Two compatible native scalar projections give a map to the native scalar
extension of the actual original étale pullback. -/
def scalarEtalePullbackLift :
    Q ⟶ (fieldBaseChange (algebraMap k L)).obj (etalePullback f g) := by
  let r := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have hc : (a.left ≫ pullback.fst X.hom r) ≫ f.left =
      (b.left ≫ pullback.fst Y.hom r) ≫ g.left := by
    have hh := congrArg (fun t => t.left ≫ pullback.fst Z.hom r) h
    change (a.left ≫ ((baseChange r).map f).left) ≫ pullback.fst Z.hom r =
      (b.left ≫ ((baseChange r).map g).left) ≫ pullback.fst Z.hom r at hh
    simpa only [Category.assoc, baseChange_map_fst] using hh
  let l := pullback.lift (a.left ≫ pullback.fst X.hom r)
    (b.left ≫ pullback.fst Y.hom r) hc
  have hl : l ≫ (etalePullback f g).hom = Q.hom ≫ r := by
    change l ≫ (pullback.snd f.left g.left ≫ Y.hom) = _
    rw [← Category.assoc, pullback.lift_snd, Category.assoc, pullback.condition]
    rw [← Category.assoc]
    exact congrArg (fun t => t ≫ r) (MorphismProperty.Over.w b)
  exact homMk (pullback.lift l Q.hom hl) (pullback.lift_snd _ _ _)

/-- The lift retains its literal native scalar first projection. -/
@[reassoc]
theorem scalarEtalePullbackLift_fst :
    scalarEtalePullbackLift f g a b h ≫
      (fieldBaseChange (algebraMap k L)).map (etalePullbackFst f g) = a := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp only [MorphismProperty.Comma.comp_left, Category.assoc, fieldBaseChange,
      baseChange_map_fst, scalarEtalePullbackLift, homMk, MorphismProperty.Over.homMk,
      Over.homMk_left, etalePullbackFst_left,
      pullback.lift_fst_assoc, pullback.lift_fst]
  · simp only [MorphismProperty.Comma.comp_left, Category.assoc, fieldBaseChange,
      baseChange_map_snd, scalarEtalePullbackLift, homMk, MorphismProperty.Over.homMk,
      Over.homMk_left, pullback.lift_snd]
    exact (MorphismProperty.Over.w a).symm

/-- The same lift retains its literal native scalar second projection. -/
@[reassoc]
theorem scalarEtalePullbackLift_snd :
    scalarEtalePullbackLift f g a b h ≫
      (fieldBaseChange (algebraMap k L)).map (etalePullbackSnd f g) = b := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp only [MorphismProperty.Comma.comp_left, Category.assoc, fieldBaseChange,
      baseChange_map_fst, scalarEtalePullbackLift, homMk, MorphismProperty.Over.homMk,
      Over.homMk_left, etalePullbackSnd_left,
      pullback.lift_fst_assoc, pullback.lift_snd]
  · simp only [MorphismProperty.Comma.comp_left, Category.assoc, fieldBaseChange,
      baseChange_map_snd, scalarEtalePullbackLift, homMk, MorphismProperty.Over.homMk,
      Over.homMk_left, pullback.lift_snd]
    exact (MorphismProperty.Over.w b).symm

end Motivic.SmoothSite
