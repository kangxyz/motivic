/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.ChartMarkedNorm
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.Boundary

/-! # The actual correction chart and original target marked coordinate

The parameter is the genuine fixed A, not the original source Y. Both marked
factors come from one original source chart point and the original finite map.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.TargetMarkedCoordinate`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S X Y A Z C P T V Q : Scheme.{u}}
  (q : X ⟶ S) (π : P ⟶ S) (f : C ⟶ P)
  (jB : Y ⟶ C) (jA : X ⟶ P) (p : Y ⟶ X)
  (hq : jB ≫ (f ≫ π) = p ≫ q)
  (hret : jB ≫ f = p ≫ jA) (hA : jA ≫ π = q)
  (a : A ⟶ X) (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (k : V ⟶ T) (σ : Q ⟶ V) (u : T ⟶ C) (m : Q ⟶ Z)
  (hj : m ≫ (s ≫ jB) = (σ ≫ k) ≫ u)
  (w : T ⟶ pullback (a ≫ q) (f ≫ π))
  (hw : w ≫ pullback.snd (a ≫ q) (f ≫ π) = u)

/-- The original finite map and fixed parameter define the native target point. -/
def correctionMarkedTargetAmbient : Q ⟶ pullback (jA ≫ π) π :=
  pullback.lift ((σ ≫ k) ≫ w ≫ pullback.fst (a ≫ q) (f ≫ π) ≫ a)
    ((σ ≫ k) ≫ u ≫ f) (by
      calc
        _ = (σ ≫ k) ≫ w ≫ pullback.fst (a ≫ q) (f ≫ π) ≫ (a ≫ q) := by
          simp only [Category.assoc, hA]
        _ = (σ ≫ k) ≫ w ≫ pullback.snd (a ≫ q) (f ≫ π) ≫ (f ≫ π) := by
          rw [pullback.condition]
        _ = _ := by
          rw [← Category.assoc w, hw]
          simp only [Category.assoc])

include hret hs hj in
/-- The target point is marked by the SAME original marked point. -/
theorem correctionMarkedTargetAmbient_point :
    correctionMarkedTargetAmbient q π f jA hA a k σ u w hw ≫
      pullback.snd (jA ≫ π) π = m ≫ z ≫ jA := by
  simp only [correctionMarkedTargetAmbient, pullback.lift_snd]
  rw [← Category.assoc (σ ≫ k), ← hj]
  simp only [Category.assoc, hret, ← Category.assoc s, hs]

/-- The native target marked factor is constructed, not supplied separately. -/
def correctionNativeTargetMarkedFactor : Q ⟶ pullback (jA ≫ π) (z ≫ jA ≫ π) :=
  (Hom.graphBoundaryRestriction_isPullback π jA z).lift
    (correctionMarkedTargetAmbient q π f jA hA a k σ u w hw) m
    (correctionMarkedTargetAmbient_point q π f jB jA p hret hA a z s hs
      k σ u m hj w hw)

/-- The actual correction marked factor and original target factor have exactly
the same graph-coordinate map, via the general common-zero identity. -/
theorem correctionChart_targetMarked_coordinate_eq :
    correctionChartMarkedFactor q (f ≫ π) jB p hq a z s hs k σ u m hj w hw ≫
      Hom.boundaryProductMap q a z =
    correctionNativeTargetMarkedFactor q π f jB jA p hret hA a z s hs
      k σ u m hj w hw ≫
      (Hom.relativeBoundaryProductIso q π jA (𝟙 X) (by simpa using hA)
        z z (by simp)).hom ≫ Hom.boundaryProductMap q (𝟙 X) z := by
  let μ := correctionChartMarkedFactor q (f ≫ π) jB p hq a z s hs k σ u m hj w hw
  let ν : Q ⟶ commonZero π jA a z :=
    pullback.lift (μ ≫ pullback.fst (a ≫ q) (z ≫ q))
      (μ ≫ pullback.snd (a ≫ q) (z ≫ q)) (by
        simpa only [commonProjection, Category.assoc, hA] using
          congrArg (fun l => μ ≫ l) (pullback.condition (f := a ≫ q) (g := z ≫ q)))
  have hparameter :
      correctionNativeTargetMarkedFactor q π f jB jA p hret hA a z s hs
        k σ u m hj w hw ≫ pullback.fst (jA ≫ π) (z ≫ jA ≫ π) =
      correctionMarkedTargetAmbient q π f jA hA a k σ u w hw ≫
        pullback.fst (jA ≫ π) π := by
    have hh := congrArg (fun l => l ≫ pullback.fst (jA ≫ π) π)
      ((Hom.graphBoundaryRestriction_isPullback π jA z).lift_fst
        (correctionMarkedTargetAmbient q π f jA hA a k σ u w hw) m
        (correctionMarkedTargetAmbient_point q π f jB jA p hret hA a z s hs
          k σ u m hj w hw))
    simpa only [correctionNativeTargetMarkedFactor, Category.assoc,
      Hom.graphBoundaryRestriction, pullback.lift_fst] using hh
  have hL : ν ≫ commonZeroToLambda π jA a z =
      correctionNativeTargetMarkedFactor q π f jB jA p hret hA a z s hs
        k σ u m hj w hw := by
    apply pullback.hom_ext
    · rw [hparameter]
      simp [ν, μ, commonZeroToLambda, correctionMarkedTargetAmbient,
        correctionChartMarkedFactor]
    · simp [ν, μ, commonZeroToLambda, correctionNativeTargetMarkedFactor,
        correctionChartMarkedFactor]
  have hR : ν ≫ commonZeroToPsi q π jA (𝟙 X) (by simpa using hA)
      a a (𝟙 A) (by simp) z z (by simp) = μ := by
    apply pullback.hom_ext <;> simp [ν, commonZeroToPsi]
  rw [← hL, Category.assoc,
    commonZero_coordinate_eq q π jA (𝟙 X) (by simpa using hA)
      a a (𝟙 A) (by simp) z z (by simp),
    ← Category.assoc, hR]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
