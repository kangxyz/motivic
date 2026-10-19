/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.BaseChangeSquare

/-! # The actual chart residual maps into the full inverse thickened boundary

The residual factor is constructed from the original marked section and the
actual source base-change square. Both projections are literal, and the whole
closed boundary is pulled back without replacing it by its reduction.


Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.ThickBoundaryBaseChange`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.GraphChartFactors`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.ChartMarkedNorm`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

variable {C X Y Z C' X' Y' Z' D : Scheme.{u}}
  (f : C ⟶ X) [IsFinite f] (j : Y ⟶ C) (z : Z ⟶ X)
  (s : Z ⟶ Y) (hs : (s ≫ j) ≫ f = z)
  (f' : C' ⟶ X') [IsFinite f'] (j' : Y' ⟶ C') (z' : Z' ⟶ X')
  (s' : Z' ⟶ Y') (hs' : (s' ≫ j') ≫ f' = z')
  (u : C' ⟶ C) (t : X' ⟶ X) (Hf : IsPullback u f' f t)
  (a : Z' ⟶ Z) (hz : z' ≫ t = a ≫ z)
  (hj : a ≫ (s ≫ j) = (s' ≫ j') ≫ u)
  (d : D ⟶ C) (b : (residualMarkedFiberOpen f j z s hs).toScheme ⟶ D)
  (hb : b ≫ d = residualMarkedFiberMap f j z s hs)

/-- Original residual transport under the actual parameter/chart base change. -/
def residualBaseChangeMap :
    (residualMarkedFiberOpen f' j' z' s' hs').toScheme ⟶
      (residualMarkedFiberOpen f j z s hs).toScheme :=
  residualMarkedFiberPullbackMap f j z s hs f' j' z' s' hs' a
    (markedFiberBaseChangeMap f f' u t Hf z z' a hz)
    (markedFiberSection_baseChange_isPullback f f' u t Hf z z' a hz j j' s s' hs hs' hj)

include hb in
/-- The original residual factor into D commutes with the actual chart source map. -/
theorem residualBaseChangeMap_boundary :
    (residualBaseChangeMap f j z s hs f' j' z' s' hs' u t Hf a hz hj ≫ b) ≫ d =
      residualMarkedFiberMap f' j' z' s' hs' ≫ u := by
  rw [residualBaseChangeMap, residualMarkedFiberPullbackMap_boundary
    f j z s hs f' j' z' s' hs' a _ _ d b hb]
  simp only [markedFiberBaseChangeMap_fst, residualMarkedFiberMap, Category.assoc]

/-- The chart residual maps into the full inverse thickened boundary, constructed
from the original scheme-theoretic factorization rather than its support. -/
def residualThickBoundaryBaseChangeFactor :
    (residualMarkedFiberOpen f' j' z' s' hs').toScheme ⟶ pullback u d :=
  pullback.lift (residualMarkedFiberMap f' j' z' s' hs')
    (residualBaseChangeMap f j z s hs f' j' z' s' hs' u t Hf a hz hj ≫ b)
    (residualBaseChangeMap_boundary f j z s hs f' j' z' s' hs' u t Hf a hz hj d b hb).symm

@[reassoc (attr := simp)] theorem residualThickBoundaryBaseChangeFactor_fst :
    residualThickBoundaryBaseChangeFactor f j z s hs f' j' z' s' hs'
      u t Hf a hz hj d b hb ≫ pullback.fst u d =
        residualMarkedFiberMap f' j' z' s' hs' := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem residualThickBoundaryBaseChangeFactor_snd :
    residualThickBoundaryBaseChangeFactor f j z s hs f' j' z' s' hs'
      u t Hf a hz hj d b hb ≫ pullback.snd u d =
        residualBaseChangeMap f j z s hs f' j' z' s' hs' u t Hf a hz hj ≫ b :=
  pullback.lift_snd _ _ _

include Hf hz hj hb in
/-- Scalar one on the full inverse boundary restricts to one on the original
whole chart residual. This is an actual restriction, not a support argument. -/
theorem residual_scalar_one_of_full_boundary (c : Γ(C', ⊤))
    (hc : (pullback.fst u d).appTop c = 1) :
    (residualMarkedFiberMap f' j' z' s' hs').appTop c = 1 := by
  let r := residualThickBoundaryBaseChangeFactor f j z s hs f' j' z' s' hs'
    u t Hf a hz hj d b hb
  rw [← residualThickBoundaryBaseChangeFactor_fst f j z s hs f' j' z' s' hs'
    u t Hf a hz hj d b hb, Hom.comp_appTop]
  change r.appTop ((pullback.fst u d).appTop c) = 1
  rw [hc]
  exact map_one r.appTop.hom

end AlgebraicGeometry.Scheme
