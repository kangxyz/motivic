/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.BaseChangeSquare

/-! # The actual whole marked section on a source-open chart

Only the original marked square is Cartesian. The retained source open need
not be a Cartesian inverse image of the whole target retained open.


Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.OpenChartSection`.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- Postcomposition by the actual target open preserves the whole marked square. -/
theorem marked_isPullback_comp_mono {Y X Z P : Scheme.{u}}
    (p : Y ⟶ X) (z : Z ⟶ X) (s : Z ⟶ Y)
    (H : IsPullback s (𝟙 Z) p z) (j : X ⟶ P) [Mono j] :
    IsPullback s (𝟙 Z) (p ≫ j) (z ≫ j) := by
  have hj : IsPullback (𝟙 Y) p (p ≫ j) j :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  simpa only [Category.comp_id] using H.paste_horiz hj

variable {C X Y Z C' X' Z' : Scheme.{u}}
  (f : C ⟶ X) (j : Y ⟶ C) (z : Z ⟶ X) (s : Z ⟶ Y)
  (H : IsPullback s (𝟙 Z) (j ≫ f) z)
  (f' : C' ⟶ X') (u : C' ⟶ C) (t : X' ⟶ X) (Hf : IsPullback u f' f t)
  (z' : Z' ⟶ X') (a : Z' ⟶ Z) (hz : z' ≫ t = a ≫ z)

/-- The original marked point lifts to the actual finite chart. -/
def markedOpenChartSourcePoint : Z' ⟶ C' :=
  Hf.lift (a ≫ s ≫ j) z' (by simpa only [Category.assoc, H.w, Category.id_comp] using hz.symm)

@[reassoc (attr := simp)] theorem markedOpenChartSourcePoint_left :
    markedOpenChartSourcePoint f j z s H f' u t Hf z' a hz ≫ u = a ≫ s ≫ j :=
  Hf.lift_fst _ _ _

@[reassoc (attr := simp)] theorem markedOpenChartSourcePoint_right :
    markedOpenChartSourcePoint f j z s H f' u t Hf z' a hz ≫ f' = z' :=
  Hf.lift_snd _ _ _

/-- The marked section of the literal inverse image of the original source open. -/
def markedOpenChartSection : Z' ⟶ pullback u j :=
  pullback.lift (markedOpenChartSourcePoint f j z s H f' u t Hf z' a hz) (a ≫ s)
    ((markedOpenChartSourcePoint_left f j z s H f' u t Hf z' a hz).trans
      (Category.assoc a s j).symm)

@[reassoc (attr := simp)] theorem markedOpenChartSection_source :
    markedOpenChartSection f j z s H f' u t Hf z' a hz ≫ pullback.fst u j =
      markedOpenChartSourcePoint f j z s H f' u t Hf z' a hz := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem markedOpenChartSection_retained :
    markedOpenChartSection f j z s H f' u t Hf z' a hz ≫ pullback.snd u j = a ≫ s :=
  pullback.lift_snd _ _ _

/-- This is the entire marked pullback, not merely a section on its points. -/
theorem markedOpenChartSection_isPullback :
    IsPullback (markedOpenChartSection f j z s H f' u t Hf z' a hz) (𝟙 Z')
      (pullback.fst u j ≫ f') z' := by
  have hk := (IsPullback.of_hasPullback u j).flip.paste_vert Hf
  have ho : IsPullback
      (markedOpenChartSection f j z s H f' u t Hf z' a hz ≫ pullback.snd u j)
      (𝟙 Z') (j ≫ f) (z' ≫ t) := by
    simpa only [markedOpenChartSection_retained, hz] using
      (IsPullback.id_vert a).paste_horiz H
  apply ho.of_right _ hk
  simp only [Category.id_comp, ← Category.assoc, markedOpenChartSection_source,
    markedOpenChartSourcePoint_right]

end AlgebraicGeometry.Scheme
