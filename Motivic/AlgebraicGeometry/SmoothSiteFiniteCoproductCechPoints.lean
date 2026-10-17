/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteFiniteCovers
public import Motivic.AlgebraicGeometry.SmoothSiteNisnevichPullbacks
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Actual Čech points in pairs of finite coproduct components

The comparison from a component pair to the Čech pullback of the finite total
map is the literal scheme pullback map. It is an open immersion. Every total
Čech point with designated component projections lifts to those same component
points, with an isomorphism on its actual residue field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.SmoothSite

variable {S : Scheme.{u}} {Y : SmoothSite S} {n : ℕ} {V : Fin n → SmoothSite S}
  (q : ∀ i, V i ⟶ Y) [∀ i, Etale (q i).left]

/-- The literal pullback map from a component pair to the Čech object of the total map. -/
def finiteCoproductCechMap (i j : Fin n) :
    etalePullback (q i) (q j) ⟶
      etalePullback (finiteCoproductDesc q) (finiteCoproductDesc q) :=
  homMk (pullback.map (q i).left (q j).left
    (finiteCoproductDesc q).left (finiteCoproductDesc q).left
    (finiteCoproductι V i).left (finiteCoproductι V j).left (𝟙 Y.left)
    (by simpa only [Category.comp_id, MorphismProperty.Comma.comp_left] using
      (congrArg (fun f => f.left) (finiteCoproductι_desc q i)).symm)
    (by simpa only [Category.comp_id, MorphismProperty.Comma.comp_left] using
      (congrArg (fun f => f.left) (finiteCoproductι_desc q j)).symm)) (by
      change pullback.map _ _ _ _ _ _ _ _ _ ≫
        (pullback.snd _ _ ≫ (finiteCoproduct V).hom) =
          pullback.snd _ _ ≫ (V j).hom
      rw [← Category.assoc, pullback.lift_snd, Category.assoc, MorphismProperty.Over.w])

/-- Forgetting the smooth-site map gives the native scheme pullback map. -/
theorem finiteCoproductCechMap_left (i j : Fin n) :
    (finiteCoproductCechMap q i j).left =
      pullback.map (q i).left (q j).left
        (finiteCoproductDesc q).left (finiteCoproductDesc q).left
        (finiteCoproductι V i).left (finiteCoproductι V j).left (𝟙 Y.left)
        (by simpa only [Category.comp_id, MorphismProperty.Comma.comp_left] using
          (congrArg (fun f => f.left) (finiteCoproductι_desc q i)).symm)
        (by simpa only [Category.comp_id, MorphismProperty.Comma.comp_left] using
          (congrArg (fun f => f.left) (finiteCoproductι_desc q j)).symm) := rfl

@[reassoc (attr := simp)]
theorem finiteCoproductCechMap_fst (i j : Fin n) :
    finiteCoproductCechMap q i j ≫
        etalePullbackFst (finiteCoproductDesc q) (finiteCoproductDesc q) =
      etalePullbackFst (q i) (q j) ≫ finiteCoproductι V i := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem finiteCoproductCechMap_snd (i j : Fin n) :
    finiteCoproductCechMap q i j ≫
        etalePullbackSnd (finiteCoproductDesc q) (finiteCoproductDesc q) =
      etalePullbackSnd (q i) (q j) ≫ finiteCoproductι V j := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_snd _ _ _

instance finiteCoproductCechMap_isOpenImmersion (i j : Fin n) :
    IsOpenImmersion (finiteCoproductCechMap q i j).left := by
  rw [finiteCoproductCechMap_left]
  infer_instance

instance finiteCoproductCechMap_etale (i j : Fin n) :
    Etale (finiteCoproductCechMap q i j).left := inferInstance

/-- The component-pair map identifies the actual residue fields, as an open immersion. -/
theorem finiteCoproductCechMap_residueFieldMap_isIso (i j : Fin n)
    (w : (etalePullback (q i) (q j)).left) :
    IsIso ((finiteCoproductCechMap q i j).left.residueFieldMap w) := inferInstance

/-- An actual total Čech point lifts to its designated pair of component points.
The map to the total Čech object is an open immersion, not a replacement envelope. -/
theorem exists_finiteCoproductCechPoint (i j : Fin n)
    (vi : (V i).left) (vj : (V j).left)
    (w : (etalePullback (finiteCoproductDesc q) (finiteCoproductDesc q)).left)
    (hfst : (etalePullbackFst (finiteCoproductDesc q) (finiteCoproductDesc q)).left w =
      (finiteCoproductι V i).left vi)
    (hsnd : (etalePullbackSnd (finiteCoproductDesc q) (finiteCoproductDesc q)).left w =
      (finiteCoproductι V j).left vj) :
    ∃ w' : (etalePullback (q i) (q j)).left,
      (finiteCoproductCechMap q i j).left w' = w ∧
      (etalePullbackFst (q i) (q j)).left w' = vi ∧
      (etalePullbackSnd (q i) (q j)).left w' = vj ∧
      IsIso ((finiteCoproductCechMap q i j).left.residueFieldMap w') := by
  have hw : w ∈ Set.range (finiteCoproductCechMap q i j).left := by
    rw [finiteCoproductCechMap_left]
    exact (Scheme.Pullback.range_map (q i).left (q j).left
      (finiteCoproductDesc q).left (finiteCoproductDesc q).left
      (finiteCoproductι V i).left (finiteCoproductι V j).left (𝟙 Y.left)
      (by simpa only [Category.comp_id, MorphismProperty.Comma.comp_left] using
        (congrArg (fun f => f.left) (finiteCoproductι_desc q i)).symm)
      (by simpa only [Category.comp_id, MorphismProperty.Comma.comp_left] using
        (congrArg (fun f => f.left) (finiteCoproductι_desc q j)).symm)).ge
      ⟨⟨vi, hfst.symm⟩, ⟨vj, hsnd.symm⟩⟩
  obtain ⟨w', hw'⟩ := hw
  refine ⟨w', hw', ?_, ?_, inferInstance⟩
  · apply (finiteCoproductι V i).left.isEmbedding.injective
    have h := congrArg (fun f => f.left w') (finiteCoproductCechMap_fst q i j)
    change (etalePullbackFst (finiteCoproductDesc q) (finiteCoproductDesc q)).left
      ((finiteCoproductCechMap q i j).left w') =
        (finiteCoproductι V i).left ((etalePullbackFst (q i) (q j)).left w') at h
    rw [hw', hfst] at h
    exact h.symm
  · apply (finiteCoproductι V j).left.isEmbedding.injective
    have h := congrArg (fun f => f.left w') (finiteCoproductCechMap_snd q i j)
    change (etalePullbackSnd (finiteCoproductDesc q) (finiteCoproductDesc q)).left
      ((finiteCoproductCechMap q i j).left w') =
        (finiteCoproductι V j).left ((etalePullbackSnd (q i) (q j)).left w') at h
    rw [hw', hsnd] at h
    exact h.symm

end Motivic.SmoothSite
