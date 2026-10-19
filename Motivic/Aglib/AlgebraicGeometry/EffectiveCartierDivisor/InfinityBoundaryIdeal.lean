/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.EtaleBoundaryIdeal
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.DisjointBoundary.Trivialization

/-! # Canonical trivialization on the actual infinity boundary -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S C Y D : Scheme.{u}} (q : C ⟶ S) [IsSeparated q]
  (j : Y ⟶ C) [IsOpenImmersion j] (d : D ⟶ C)

/-- The actual base change of the second projection to infinity. -/
abbrev infinityProductMap := pullback.fst (pullback.snd (j ≫ q) q) d

omit [IsSeparated q] [IsOpenImmersion j] in
/-- The compactification graph has empty pullback to a boundary disjoint from the open. -/
theorem isEmpty_graph_infinity
    (h : Disjoint (Set.range j) (Set.range d)) :
    IsEmpty (pullback (C := Scheme) (compactificationGraph q j) (infinityProductMap q j d)) := by
  apply Scheme.isEmpty_pullback
  apply Set.disjoint_left.mpr
  rintro x ⟨y, rfl⟩ ⟨b, hb⟩
  have he := congrArg (fun v => (pullback.snd (j ≫ q) q) v) hb
  have hb' := congrArg (fun v : pullback (pullback.snd (j ≫ q) q) d ⟶ C => v b)
    (pullback.condition (f := pullback.snd (j ≫ q) q) (g := d))
  have hj : (pullback.snd (j ≫ q) q) ((compactificationGraph q j) y) = j y := by
    simp [compactificationGraph, ← Scheme.Hom.comp_apply]
  exact Set.disjoint_iff_forall_ne.mp h ⟨y, rfl⟩
    ⟨(pullback.snd (pullback.snd (j ≫ q) q) d) b, rfl⟩
    (hj.symm.trans (he.symm.trans hb'))

/-- The original ideal inclusion pulls back to a unit at infinity. This is the
canonical map itself, not an existential trivialization. -/
theorem infinity_pullbackIdealInclusion_isIso
    (h : Disjoint (Set.range j) (Set.range d)) :
    IsIso (Modules.Hom.pullbackToUnit (idealInclusion (compactificationGraph q j))
      (infinityProductMap q j d)) := by
  let i := compactificationGraph q j
  let b := infinityProductMap q j d
  let i' := pullback.snd i b
  let a := pullback.fst i b
  have : IsEmpty (pullback (C := Scheme) i b) := isEmpty_graph_infinity q j d h
  have : IsIso (idealInclusion i') := idealInclusion_isIso_of_isEmpty i'
  have : Flat (i ≫ pullback.snd (j ≫ q) q) := by
    simpa [i, compactificationGraph] using (inferInstance : Flat j)
  have : IsClosedImmersion i := by dsimp [i, compactificationGraph]; infer_instance
  have hv : IsIso (idealPullbackMap i i' b a pullback.condition) :=
    flatQuotient_idealPullbackMap_isIso (pullback.snd (j ≫ q) q) d
      (pullback.snd _ _) b i i' a pullback.condition
      (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)
  change IsIso ((Scheme.Modules.pullback b).map (idealInclusion i) ≫
    SheafOfModules.pullbackObjUnitToUnit b.toRingCatSheafHom)
  rw [← idealPullbackMap_inclusion i i' b a pullback.condition]
  infer_instance

/-- The inverse canonical ideal inclusion supplies the prescribed infinity coordinate. -/
def infinityBoundaryIdealIso (h : Disjoint (Set.range j) (Set.range d)) :
    SheafOfModules.unit (pullback (pullback.snd (j ≫ q) q) d).ringCatSheaf ≅
      (Scheme.Modules.pullback (infinityProductMap q j d)).obj
        (idealModule (compactificationGraph q j)) := by
  have := infinity_pullbackIdealInclusion_isIso q j d h
  exact (asIso (Modules.Hom.pullbackToUnit (idealInclusion (compactificationGraph q j))
    (infinityProductMap q j d))).symm

/-- Dualizing the inverse canonical ideal inclusion gives the canonical infinity
trivialization of the original graph divisor bundle. -/
def infinityBoundaryDivisorIso (h : Disjoint (Set.range j) (Set.range d))
    (hI : Invertible.IsLocallyRankOne (pullback (j ≫ q) q)
      (idealModule (compactificationGraph q j))) :
    (Scheme.Modules.pullback (infinityProductMap q j d)).obj
      (Invertible.dualLineBundle _ ⟨idealModule (compactificationGraph q j), hI⟩).val ≅
        SheafOfModules.unit (pullback (pullback.snd (j ≫ q) q) d).ringCatSheaf :=
  dualBoundaryTrivialization (infinityProductMap q j d)
    ⟨idealModule (compactificationGraph q j), hI⟩ (infinityBoundaryIdealIso q j d h)

end AlgebraicGeometry.Scheme.Hom
