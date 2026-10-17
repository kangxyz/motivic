/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteFiniteCoproductCechPoints
public import Lean.Util.CollectAxioms

/-! Actual finite-total Čech points lift to designated original components. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic.SmoothSite

universe u

namespace MotivicTest.SmoothSiteFiniteCoproductCechPoints

variable {S : Scheme.{u}} {Y : Motivic.SmoothSite S} {n : ℕ}
  {V : Fin n → Motivic.SmoothSite S} (q : ∀ i, V i ⟶ Y) [∀ i, Etale (q i).left]

/-- The component-pair comparison is definitionally the native scheme pullback map. -/
theorem actual_pair_map_is_literal (i j : Fin n) :
    (finiteCoproductCechMap q i j).left =
      pullback.map (q i).left (q j).left
        (finiteCoproductDesc q).left (finiteCoproductDesc q).left
        (finiteCoproductι V i).left (finiteCoproductι V j).left (𝟙 Y.left)
        (by simpa only [Category.comp_id, MorphismProperty.Comma.comp_left] using
          (congrArg (fun f => f.left) (finiteCoproductι_desc q i)).symm)
        (by simpa only [Category.comp_id, MorphismProperty.Comma.comp_left] using
          (congrArg (fun f => f.left) (finiteCoproductι_desc q j)).symm) := rfl

/-- No residue-field or matching premise is supplied to the point-lifting theorem. -/
theorem actual_designated_point_lift (i j : Fin n)
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
      IsIso ((finiteCoproductCechMap q i j).left.residueFieldMap w') :=
  exists_finiteCoproductCechPoint q i j vi vj w hfst hsnd

open Lean in
run_cmd do
  for name in #[``actual_pair_map_is_literal, ``actual_designated_point_lift,
      ``finiteCoproductCechMap_isOpenImmersion, ``finiteCoproductCechMap_etale,
      ``finiteCoproductCechMap_residueFieldMap_isIso,
      ``finiteCoproductCechMap_fst, ``finiteCoproductCechMap_snd] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual finite-coproduct Čech point lifting: standard foundations only."

end MotivicTest.SmoothSiteFiniteCoproductCechPoints
