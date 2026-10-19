/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.Boundary
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RetainedMarkedChartProjection

/-! # The same marked coordinate on the original source and retained target

Both factors are built from the actual source chart point. The comparison uses
its original parameter and marked projections, and the existing common-boundary
coordinate identity. It does not identify independently chosen frames.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.RetainedMarkedCoordinateComparison`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.RetainedTargetNativeScalar`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Norm.RetainedPrescribedGraph`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Norm.RetainedSectionPairGraph`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairNativeTargetScalar`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.RelativeCurvePencil
universe u
namespace AlgebraicGeometry.Scheme.Hom

@[reassoc (attr := simp)] private theorem graph_boundary_lift_parameter
    {S C Y Z Q : Scheme.{u}} (π : C ⟶ S) (j : Y ⟶ C) (s : Z ⟶ Y)
    (γ : Q ⟶ pullback (j ≫ π) π) (a : Q ⟶ Z)
    (h : γ ≫ pullback.snd (j ≫ π) π = a ≫ (s ≫ j)) :
    (graphBoundaryRestriction_isPullback π j s).lift γ a h ≫
      pullback.fst (j ≫ π) (s ≫ j ≫ π) = γ ≫ pullback.fst (j ≫ π) π := by
  have hh := congrArg (fun m => m ≫ pullback.fst (j ≫ π) π)
    ((graphBoundaryRestriction_isPullback π j s).lift_fst γ a h)
  simpa only [Category.assoc, graphBoundaryRestriction, pullback.lift_fst] using hh

variable {S X Y Z C P Q : Scheme.{u}} (q : X ⟶ S) (π : P ⟶ S)
  (f : C ⟶ P) (jB : Y ⟶ C) (jA : X ⟶ P) (p : Y ⟶ X)
  (hret : jB ≫ f = p ≫ jA) (hA : jA ≫ π = q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (γ : Q ⟶ pullback (jB ≫ f ≫ π) (f ≫ π)) (a : Q ⟶ Z)
  (hpoint : γ ≫ pullback.snd (jB ≫ f ≫ π) (f ≫ π) = a ≫ s ≫ jB)

include hret hA in
theorem retained_source_structure : jB ≫ (f ≫ π) = p ≫ q := by
  rw [← Category.assoc, hret, Category.assoc, hA]

/-- The actual marked source factor, with no independent factor choice. -/
def retainedSourceMarkedFactor : Q ⟶ pullback (jB ≫ (f ≫ π)) (s ≫ jB ≫ (f ≫ π)) :=
  (graphBoundaryRestriction_isPullback (f ≫ π) jB s).lift γ a hpoint

/-- The same chart point in the native target product. -/
def retainedMarkedTargetAmbient : Q ⟶ pullback (jA ≫ π) π :=
  γ ≫ graphProductMap π f jB ≫ retainedParameterProductMap π f jB jA p hret

include hs hpoint in
theorem retainedMarkedTargetAmbient_point :
    retainedMarkedTargetAmbient π f jB jA p hret γ ≫ pullback.snd (jA ≫ π) π =
      a ≫ z ≫ jA := by
  simp only [retainedMarkedTargetAmbient, Category.assoc,
    retainedParameterProductMap_snd, graphProductMap_snd]
  rw [← Category.assoc γ, hpoint]
  simp only [Category.assoc, hret, ← Category.assoc s, hs]

/-- The target marked factor is built from the same original chart point. -/
def retainedNativeTargetMarkedFactor : Q ⟶ pullback (jA ≫ π) (z ≫ jA ≫ π) :=
  (graphBoundaryRestriction_isPullback π jA z).lift
    (retainedMarkedTargetAmbient π f jB jA p hret γ) a
    (retainedMarkedTargetAmbient_point π f jB jA p hret z s hs γ a hpoint)

/-- The literal selected inverse-frame chart has the same target ambient point
as the original source chart under the original finite graph-product map. -/
theorem retainedMarkedChart_ambient {T W V : Scheme.{u}}
    (v : T ⟶ pullback (jB ≫ f ≫ π) (f ≫ π)) (n : T ⟶ W)
    (w : W ⟶ pullback (jB ≫ f ≫ π) π)
    (hn : v ≫ graphProductMap π f jB = n ≫ w)
    (e : V ⟶ pullback (jA ≫ π) π)
    (l : W ⟶ pullback (retainedParameterProductMap π f jB jA p hret) e)
    (hl : l ≫ pullback.fst (retainedParameterProductMap π f jB jA p hret) e = w)
    (δ : Q ⟶ T) :
    δ ≫ n ≫ l ≫ pullback.snd (retainedParameterProductMap π f jB jA p hret) e ≫ e =
      retainedMarkedTargetAmbient π f jB jA p hret (δ ≫ v) := by
  calc
    _ = δ ≫ n ≫ l ≫
        pullback.fst (retainedParameterProductMap π f jB jA p hret) e ≫
          retainedParameterProductMap π f jB jA p hret := by
      exact congrArg (fun m => δ ≫ n ≫ l ≫ m)
        (pullback.condition (f := retainedParameterProductMap π f jB jA p hret)
          (g := e)).symm
    _ = δ ≫ n ≫ w ≫ retainedParameterProductMap π f jB jA p hret := by
      rw [← Category.assoc l, hl]
    _ = retainedMarkedTargetAmbient π f jB jA p hret (δ ≫ v) := by
      simpa only [retainedMarkedTargetAmbient, Category.assoc] using
        congrArg (fun m => δ ≫ m ≫ retainedParameterProductMap π f jB jA p hret) hn.symm

/-- The original source and native target factors have the identical marked
coordinate map. The common source parameter is the original `Y`, not a newly
chosen correction parameter. -/
theorem retainedMarkedCoordinate_eq :
    retainedSourceMarkedFactor π f jB s γ a hpoint ≫
      (relativeBoundaryProductIso q (f ≫ π) jB p
        (retained_source_structure q π f jB jA p hret hA) z s hs).hom ≫
        boundaryProductMap q p z =
    retainedNativeTargetMarkedFactor π f jB jA p hret z s hs γ a hpoint ≫
      (relativeBoundaryProductIso q π jA (𝟙 X) (by simpa using hA)
        z z (by simp)).hom ≫ boundaryProductMap q (𝟙 X) z := by
  let ν : Q ⟶ commonZero (f ≫ π) jB (𝟙 Y) s :=
    pullback.lift (γ ≫ pullback.fst _ _) a (by
      simp only [commonProjection, Category.id_comp, Category.assoc]
      rw [pullback.condition, ← Category.assoc γ, hpoint]
      simp only [Category.assoc])
  have hL : ν ≫ commonZeroToLambda (f ≫ π) jB (𝟙 Y) s =
      retainedSourceMarkedFactor π f jB s γ a hpoint := by
    apply pullback.hom_ext <;>
      simp [ν, commonZeroToLambda, retainedSourceMarkedFactor]
  have hR : ν ≫ commonZeroToPsi q (f ≫ π) jB p
      (retained_source_structure q π f jB jA p hret hA)
      (𝟙 X) (𝟙 Y) p (by simp) z s hs ≫ boundaryProductMap q (𝟙 X) z =
      retainedNativeTargetMarkedFactor π f jB jA p hret z s hs γ a hpoint ≫
        (relativeBoundaryProductIso q π jA (𝟙 X) (by simpa using hA)
          z z (by simp)).hom ≫ boundaryProductMap q (𝟙 X) z := by
    apply pullback.hom_ext <;>
      simp [ν, commonZeroToPsi, boundaryProductMap, relativeBoundaryProductIso,
        retainedNativeTargetMarkedFactor, retainedMarkedTargetAmbient,
        retainedParameterProductMap, retainedParameterProductIso, parameterProductMap]
  rw [← hL, Category.assoc, commonZero_coordinate_eq]
  exact hR

end AlgebraicGeometry.Scheme.Hom
