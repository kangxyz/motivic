/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RetainedParameterGraph

/-! # The literal marked projection on the same inverse target chart

The actual marked Cartesian chart square, together with the selected chart's
inverse-frame factorization, supplies the prescribed target scalar's marked
projection equation. No scalar or separate marked factor is assumed.


Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RetainedMarkedChartProjection`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.RetainedMarkedCoordinateComparison`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S C P X Y : Scheme.{u}} (q : P ⟶ S) (f : C ⟶ P)
  (jB : Y ⟶ C) (jA : X ⟶ P) (p : Y ⟶ X) (h : jB ≫ f = p ≫ jA)

@[reassoc (attr := simp)] theorem retainedParameterProductMap_snd :
    retainedParameterProductMap q f jB jA p h ≫ pullback.snd (jA ≫ q) q =
      pullback.snd (jB ≫ f ≫ q) q := by
  simp [retainedParameterProductMap, retainedParameterProductIso]

/-- The canonical marked chart gives the exact original marked-point equation
in the SAME target frame domain. -/
theorem retainedMarkedChart_projection {V W Z Q : Scheme.{u}}
    (v : V ⟶ pullback (jA ≫ q) q) (w : W ⟶ pullback (jB ≫ f ≫ q) q)
    (l : W ⟶ pullback (retainedParameterProductMap q f jB jA p h) v)
    (hl : l ≫ pullback.fst (retainedParameterProductMap q f jB jA p h) v = w)
    (z : Z ⟶ P) (a : Q ⟶ Z) (z' : Q ⟶ W)
    (Hz : IsPullback a z' z (w ≫ pullback.snd (jB ≫ f ≫ q) q)) :
    (z' ≫ l ≫ pullback.snd (retainedParameterProductMap q f jB jA p h) v ≫ v) ≫
        pullback.snd (jA ≫ q) q = a ≫ z := by
  calc
    _ = z' ≫ l ≫ pullback.fst (retainedParameterProductMap q f jB jA p h) v ≫
        retainedParameterProductMap q f jB jA p h ≫ pullback.snd (jA ≫ q) q := by
      exact congrArg (fun m => z' ≫ l ≫ m ≫ pullback.snd (jA ≫ q) q)
        (pullback.condition (f := retainedParameterProductMap q f jB jA p h)
          (g := v)).symm
    _ = z' ≫ w ≫ pullback.snd (jB ≫ f ≫ q) q := by
      rw [retainedParameterProductMap_snd, ← Category.assoc l, hl]
    _ = a ≫ z := Hz.w.symm

end AlgebraicGeometry.Scheme.Hom
