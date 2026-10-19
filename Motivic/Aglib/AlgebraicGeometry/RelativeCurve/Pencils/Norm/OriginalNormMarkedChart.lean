/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalRetainedNormMaps
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.OpenChartSection
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.TargetMarkedCoordinate
/-! # Actual marked charts for an arbitrary original norm parameter

The compactified norm map, its chart, and a test map into the full marked
boundary determine every source-chart and marked-section map. Only the original
marked square is required; the retained second-factor square is not assumed
Cartesian. The test scheme can have nilpotents and need not be a field.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormMarkedChart`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Correction.OriginalCorrectionNormChart`, `Norm.SectionPairNormNeighborhood`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.RelativeCurvePencil
universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S C P A Y Z W Q : Scheme.{u}}
  (π : P ⟶ S) (f : C ⟶ P) (b : A ⟶ S)
  (j : Y ⟶ C) (z : Z ⟶ P) (s : Z ⟶ Y)
  (H : IsPullback s (𝟙 Z) (j ≫ f) z)
  (w : W ⟶ pullback b π)

/-- The actual finite source chart's map to the original compactification. -/
abbrev normChartSourceMap : pullback (normProductMap π f b) w ⟶ C :=
  pullback.fst (normProductMap π f b) w ≫ pullback.snd b (f ≫ π)

/-- Cartesianity follows from the two actual base changes. -/
theorem normChartSourceMap_isPullback :
    IsPullback (normChartSourceMap π f b w)
      (pullback.snd (normProductMap π f b) w) f (w ≫ pullback.snd b π) :=
  (IsPullback.of_hasPullback (normProductMap π f b) w).paste_horiz
    (normProductMap_isPullback π f b)

/-- The full marked product is an actual scheme, not its set of reduced points. -/
abbrev normMarkedProductMap : pullback b (z ≫ π) ⟶ pullback b π :=
  retainedProductInclusion b π z

variable (e : Q ⟶ pullback (normMarkedProductMap π b z) w)

/-- The marked point obtained from the actual boundary-test projection. -/
abbrev normChartMarkedPoint : Q ⟶ Z :=
  e ≫ pullback.fst (normMarkedProductMap π b z) w ≫ pullback.snd b (z ≫ π)

/-- The chart-test map obtained from the same full-boundary test. -/
abbrev normChartMarkedBase : Q ⟶ W :=
  e ≫ pullback.snd (normMarkedProductMap π b z) w

/-- The two test projections identify the SAME original marked point. -/
theorem normChartMarkedPoint_base :
    normChartMarkedBase π b z w e ≫ (w ≫ pullback.snd b π) =
      normChartMarkedPoint π b z w e ≫ z := by
  simpa only [normChartMarkedBase, normChartMarkedPoint, Category.assoc,
    normMarkedProductMap, retainedProductInclusion_snd] using
    congrArg (fun l => e ≫ l ≫ pullback.snd b π)
      (pullback.condition (f := normMarkedProductMap π b z) (g := w)).symm

/-- For the whole affine boundary chart, the marked point square is Cartesian.
This transports actual boundary flatness; an arbitrary test map alone would not suffice. -/
theorem normChartMarkedPoint_isPullback [IsIso e] :
    IsPullback (normChartMarkedPoint π b z w e) (normChartMarkedBase π b z w e)
      z (w ≫ pullback.snd b π) := by
  have Hwhole := (IsPullback.of_hasPullback (normMarkedProductMap π b z) w).paste_horiz
    (retainedProductInclusion_isPullback b π z)
  exact Hwhole.of_iso' (asIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [normChartMarkedPoint])
    (by simp [normChartMarkedBase]) (by simp) (by simp)

/-- The literal inverse image of the original source open carries the marked section. -/
abbrev normChartMarkedSection :
    Q ⟶ pullback (normChartSourceMap π f b w) j :=
  markedOpenChartSection f j z s H (pullback.snd (normProductMap π f b) w)
    (normChartSourceMap π f b w) (w ≫ pullback.snd b π)
    (normChartSourceMap_isPullback π f b w)
    (normChartMarkedBase π b z w e) (normChartMarkedPoint π b z w e)
    (normChartMarkedPoint_base π b z w e)

/-- The marked section satisfies the exact finite-chart equation. -/
@[reassoc]
theorem normChartMarkedSection_base :
    (normChartMarkedSection π f b j z s H w e ≫
      pullback.fst (normChartSourceMap π f b w) j) ≫
      pullback.snd (normProductMap π f b) w = normChartMarkedBase π b z w e := by
  simp [normChartMarkedSection]

/-- The marked source point maps to the literal target-chart point. -/
theorem normChartMarkedSection_product :
    (normChartMarkedSection π f b j z s H w e ≫
      pullback.fst (normChartSourceMap π f b w) j) ≫
        pullback.fst (normProductMap π f b) w ≫ normProductMap π f b =
      normChartMarkedBase π b z w e ≫ w := by
  rw [pullback.condition, ← Category.assoc, normChartMarkedSection_base]

/-- The source compactification projection is the original marked section. -/
theorem normChartMarkedSection_original :
    normChartMarkedPoint π b z w e ≫ (s ≫ j) =
      (normChartMarkedSection π f b j z s H w e ≫
        pullback.fst (normChartSourceMap π f b w) j) ≫ normChartSourceMap π f b w := by
  simp [normChartMarkedSection, Category.assoc]

/-- The WHOLE marked chart square is produced by the original marked square. -/
theorem normChartMarkedSection_isPullback :
    IsPullback (normChartMarkedSection π f b j z s H w e) (𝟙 Q)
      (pullback.fst (normChartSourceMap π f b w) j ≫
        pullback.snd (normProductMap π f b) w) (normChartMarkedBase π b z w e) :=
  markedOpenChartSection_isPullback f j z s H (pullback.snd (normProductMap π f b) w)
    (normChartSourceMap π f b w) (w ≫ pullback.snd b π)
    (normChartSourceMap_isPullback π f b w)
    (normChartMarkedBase π b z w e) (normChartMarkedPoint π b z w e)
    (normChartMarkedPoint_base π b z w e)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- The native target ambient map uses exactly the original norm map and parameter map. -/
theorem correctionMarkedTargetAmbient_eq_normProductMap
    {S X A C P T V Q : Scheme.{u}}
    (q : X ⟶ S) (π : P ⟶ S) (f : C ⟶ P) (jA : X ⟶ P)
    (hA : jA ≫ π = q) (a : A ⟶ X)
    (k : V ⟶ T) (σ : Q ⟶ V) (u : T ⟶ C)
    (w : T ⟶ pullback (a ≫ q) (f ≫ π))
    (hw : w ≫ pullback.snd (a ≫ q) (f ≫ π) = u) :
    correctionMarkedTargetAmbient q π f jA hA a k σ u w hw =
      (σ ≫ k) ≫ w ≫ Hom.normProductMap π f (a ≫ q) ≫
        Hom.retainedNormParameterMap π (a ≫ q) jA a (by rw [hA]) := by
  apply pullback.hom_ext
  · simp [correctionMarkedTargetAmbient, Hom.retainedNormParameterMap, Category.assoc]
  · dsimp only [correctionMarkedTargetAmbient, Hom.retainedNormParameterMap]
    simp only [Category.assoc, pullback.lift_snd, constantSourceMapOfEq_snd,
      Hom.normProductMap_snd]
    rw [← Category.assoc w, hw]

/-- The actual full-boundary test determines the exact target ambient equation
used by the marked product calculation. No independent ambient identification is supplied. -/
theorem originalNormChartMarked_target_ambient
    {S X A C P Y Z W Q : Scheme.{u}}
    (q : X ⟶ S) (π : P ⟶ S) (f : C ⟶ P) (jA : X ⟶ P)
    (hA : jA ≫ π = q) (a : A ⟶ X)
    (j : Y ⟶ C) (z : Z ⟶ P) (s : Z ⟶ Y)
    (H : IsPullback s (𝟙 Z) (j ≫ f) z)
    (w : W ⟶ pullback (a ≫ q) π)
    (e : Q ⟶ pullback (Hom.normMarkedProductMap π (a ≫ q) z) w) :
    Hom.normChartMarkedBase π (a ≫ q) z w e ≫
        (w ≫ Hom.retainedNormParameterMap π (a ≫ q) jA a (by rw [hA])) =
      correctionMarkedTargetAmbient q π f jA hA a
        (pullback.fst (Hom.normChartSourceMap π f (a ≫ q) w) j)
        (Hom.normChartMarkedSection π f (a ≫ q) j z s H w e)
        (Hom.normChartSourceMap π f (a ≫ q) w)
        (pullback.fst (Hom.normProductMap π f (a ≫ q)) w) rfl := by
  rw [correctionMarkedTargetAmbient_eq_normProductMap]
  simpa only [Category.assoc] using
    (congrArg (fun l => l ≫ Hom.retainedNormParameterMap π (a ≫ q) jA a (by rw [hA]))
      (Hom.normChartMarkedSection_product π f (a ≫ q) j z s H w e)).symm

end AlgebraicGeometry.Scheme.RelativeCurvePencil
