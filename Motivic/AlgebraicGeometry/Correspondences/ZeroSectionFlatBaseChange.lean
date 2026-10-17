/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.FlatSpanBaseChange
public import Motivic.AlgebraicGeometry.Correspondences.PolynomialPencilCycles

/-! # Flat graph restriction of actual line-bundle zero sections -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PolynomialBoundaryPencil

universe u

namespace Motivic.ZeroSectionFlatBaseChange

variable {k : Type u} [Field k] {X T Y : SmoothSite (Spec (.of k))}
  {C D : Scheme.{u}} (q : C ⟶ T.left) (r : C ⟶ Y.left)
  (h : q ≫ T.hom = r ≫ Y.hom) (α : X ⟶ T) [Flat α.left]
  (j : D ⟶ C) (p : D ⟶ X.left) (hs : IsPullback j p q α.left)
  (L : LineBundle C) (a : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
  [IsFinite (Hom.zeroInclusion a ≫ q)] [Flat (Hom.zeroInclusion a ≫ q)]

include hs in
omit r h [Flat α.left] in
/-- Base change itself supplies finiteness and flatness of the actual pulled section. -/
theorem pulled_finite_flat :
    IsFinite (Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ p) ∧
      Flat (Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ p) := by
  let e := zeroFibreOverIso j p q α.left hs L a
  have he : Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ p =
      e.inv ≫ pullback.fst α.left (Hom.zeroInclusion a ≫ q) := by
    rw [← zeroFibreOverIso_hom_base j p q α.left hs L a]
    simp [e]
  rw [he]
  exact ⟨inferInstance, inferInstance⟩

variable [Smooth (q ≫ T.hom)] [IsSeparated (q ≫ T.hom)] [QuasiCompact (q ≫ T.hom)]

/-- The original whole zero span pulls back to the literal pulled-back section.
Only the ambient square is assumed Cartesian; no correspondence equation is supplied. -/
theorem graph_zeroSection :
    letI := (pulled_finite_flat q α j p hs L a).1
    letI := (pulled_finite_flat q α j p hs L a).2
    (Cor.graphFunctor k).map α ≫
        Cor.ofFiniteFlatSpan (Hom.zeroInclusion a ≫ q) (Hom.zeroInclusion a ≫ r)
          (by simp only [Category.assoc, h]) =
      Cor.ofFiniteFlatSpan (Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ p)
        (Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ j ≫ r)
        (by
          have hp : p ≫ X.hom = (j ≫ r) ≫ Y.hom := by
            rw [Category.assoc, ← h, ← Category.assoc, hs.w,
              Category.assoc, MorphismProperty.Over.w]
          simpa only [Category.assoc] using
            congrArg (fun z => Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ z) hp) := by
  let := (pulled_finite_flat q α j p hs L a).1
  let := (pulled_finite_flat q α j p hs L a).2
  let R := SmoothSite.mk (q ≫ T.hom)
  let i : Hom.zeroScheme a ⟶ R.left := Hom.zeroInclusion a
  have hi : (Hom.zeroInclusion a ≫ q) ≫ T.hom = i ≫ R.hom := by
    exact Category.assoc _ _ _
  have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (Hom.zeroInclusion a))
  have : IsClosedImmersion (pullback.lift (Hom.zeroInclusion a ≫ q) i hi) := by
    have : IsClosedImmersion (pullback.lift (Hom.zeroInclusion a ≫ q) i hi ≫
        pullback.snd T.hom R.hom) := by
      rw [pullback.lift_snd]
      infer_instance
    exact IsClosedImmersion.of_comp _ (pullback.snd _ _)
  let g : R ⟶ Y := SmoothSite.homMk r h.symm
  have he := Cor.graph_ofFiniteFlatSpan_of_flat_postcompose
    (X := X) (T := T) (Y := R) (Z := Y) (Hom.zeroInclusion a ≫ q) i hi α g
  simp only [g, i, SmoothSite.homMk_left] at he
  refine he.trans ?_
  exact PolynomialPencilCycles.span_eq_of_iso (zeroFibreOverIso j p q α.left hs L a)
    _ _ _ _ _ _ (zeroFibreOverIso_hom_base j p q α.left hs L a)
    (by simpa only [Category.assoc] using
      zeroFibreOverIso_hom_total_assoc j p q α.left hs L a r)

end Motivic.ZeroSectionFlatBaseChange
