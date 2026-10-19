/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.ResidualFiberPullback

/-! # The actual marked fiber square under parameter and chart base change

Native pullback pasting constructs the whole finite-fiber square. Its original
marked sections give the marked Cartesian square by cancellation, so residual
transport does not require a separately supplied marked-square witness.


Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.BaseChangeSquare`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.OpenChartSection`,
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.ThickBoundaryBaseChange`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

variable {C X Z C' X' Z' : Scheme.{u}}
  (f : C ⟶ X) (f' : C' ⟶ X') (u : C' ⟶ C) (t : X' ⟶ X)
  (Hf : IsPullback u f' f t) (z : Z ⟶ X) (z' : Z' ⟶ X')
  (a : Z' ⟶ Z) (hz : z' ≫ t = a ≫ z)

/-- The original whole-fiber comparison keeps both source and marked projections. -/
def markedFiberBaseChangeMap : pullback f' z' ⟶ pullback f z :=
  pullback.lift (pullback.fst f' z' ≫ u) (pullback.snd f' z' ≫ a) (by
    rw [Category.assoc, Hf.w, ← Category.assoc, pullback.condition,
      Category.assoc, hz, Category.assoc])

@[reassoc (attr := simp)] theorem markedFiberBaseChangeMap_fst :
    markedFiberBaseChangeMap f f' u t Hf z z' a hz ≫ pullback.fst f z =
      pullback.fst f' z' ≫ u := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem markedFiberBaseChangeMap_snd :
    markedFiberBaseChangeMap f f' u t Hf z z' a hz ≫ pullback.snd f z =
      pullback.snd f' z' ≫ a := pullback.lift_snd _ _ _

/-- Pasting the original base-change square constructs the whole-fiber square. -/
theorem markedFiberBaseChangeMap_isPullback :
    IsPullback (markedFiberBaseChangeMap f f' u t Hf z z' a hz)
      (pullback.snd f' z') (pullback.snd f z) a := by
  have ho := (IsPullback.of_hasPullback f' z').paste_horiz Hf
  have ho' : IsPullback
      (markedFiberBaseChangeMap f f' u t Hf z z' a hz ≫ pullback.fst f z)
      (pullback.snd f' z') f (a ≫ z) := by
    simpa only [markedFiberBaseChangeMap_fst, hz] using ho
  exact ho'.of_right (markedFiberBaseChangeMap_snd f f' u t Hf z z' a hz)
    (IsPullback.of_hasPullback f z)

/-- Actual compatible marked sections give their Cartesian square without an
independent marked-pullback assumption. -/
theorem markedSection_isPullback_of_fiber_baseChange
    (m : Z ⟶ pullback f z) (m' : Z' ⟶ pullback f' z')
    (hm : m ≫ pullback.snd f z = 𝟙 Z)
    (hm' : m' ≫ pullback.snd f' z' = 𝟙 Z')
    (hc : a ≫ m = m' ≫ markedFiberBaseChangeMap f f' u t Hf z z' a hz) :
    IsPullback a m' m (markedFiberBaseChangeMap f f' u t Hf z z' a hz) := by
  have ho : IsPullback a (m' ≫ pullback.snd f' z') (m ≫ pullback.snd f z) a := by
    rw [hm, hm']
    exact IsPullback.id_vert a
  exact ho.of_bot hc (markedFiberBaseChangeMap_isPullback f f' u t Hf z z' a hz)

/-- The original marked-fiber sections satisfy the required Cartesian square
from the actual source-section base-change equation. -/
theorem markedFiberSection_baseChange_isPullback
    {Y Y' : Scheme.{u}} (j : Y ⟶ C) (j' : Y' ⟶ C')
    (s : Z ⟶ Y) (s' : Z' ⟶ Y')
    (hs : (s ≫ j) ≫ f = z) (hs' : (s' ≫ j') ≫ f' = z')
    (hj : a ≫ (s ≫ j) = (s' ≫ j') ≫ u) :
    IsPullback a (markedFiberSection f' j' z' s' hs')
      (markedFiberSection f j z s hs)
      (markedFiberBaseChangeMap f f' u t Hf z z' a hz) := by
  apply markedSection_isPullback_of_fiber_baseChange f f' u t Hf z z' a hz
    _ _ (markedFiberSection_snd ..) (markedFiberSection_snd ..)
  apply pullback.hom_ext
  · simpa only [Category.assoc, markedFiberSection_fst, markedFiberSection_fst_assoc,
      markedFiberBaseChangeMap_fst] using hj
  · simp only [Category.assoc, markedFiberSection_snd, markedFiberSection_snd_assoc,
      markedFiberBaseChangeMap_snd, Category.comp_id]

end AlgebraicGeometry.Scheme
