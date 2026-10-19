/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.StaticBoundaryPencilAction
public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.ZeroSectionFlat


/-! # Original boundary functionals under flat parameter restriction

Left graph composition is the whole zero span of the literal pulled functional
on the actual Cartesian retained curve. Neither a new section nor a replacement
zero cycle is chosen. The original compactification supplies finite flatness.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

universe u
namespace Motivic.Cor

/-- Flat parameter restriction of the original boundary correspondence is the
literal whole zero span of its pulled functional. The actual retained square,
not a correspondence identity or a new section choice, is the input. -/
theorem graph_boundaryFunctional_of_flat
    {k : Type u} [Field k] (X T Y : SmoothSite (Spec (.of k))) [IsAffine T.left]
    {C B U U' : Scheme.{u}} (i : B ⟶ C) (q : C ⟶ T.left) [IsProper q]
    (j : U ⟶ C) [IsOpenImmersion j] [U.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)] (L : LineBundle C)
    (a : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    [IsIso ((Scheme.Modules.pullback i).map a)]
    (hc : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range i)
    (g : U ⟶ Y.left) (hb : (j ≫ q) ≫ T.hom = g ≫ Y.hom)
    (α : X ⟶ T) [Flat α.left]
    (v : U' ⟶ U) (p : U' ⟶ X.left) (H : IsPullback v p (j ≫ q) α.left) :
    let aU := Hom.pullbackToUnit a j
    let LU := pullbackLineBundle j L
    let : IsFinite (Hom.zeroInclusion aU ≫ (j ≫ q)) :=
      (boundaryFunctional_finite_flat T i q j L a hc).1
    let : Flat (Hom.zeroInclusion aU ≫ (j ≫ q)) :=
      (boundaryFunctional_finite_flat T i q j L a hc).2
    let : IsFinite (Hom.zeroInclusion (Hom.pullbackToUnit aU v) ≫ p) :=
      (ZeroSectionFlatBaseChange.pulled_finite_flat (j ≫ q) α v p H LU aU).1
    let : Flat (Hom.zeroInclusion (Hom.pullbackToUnit aU v) ≫ p) :=
      (ZeroSectionFlatBaseChange.pulled_finite_flat (j ≫ q) α v p H LU aU).2
    (graphFunctor k).map α ≫ boundaryFunctional T Y i q j L a hc g hb =
      ofFiniteFlatSpan (X := X) (Y := Y)
        (Hom.zeroInclusion (Hom.pullbackToUnit aU v) ≫ p)
        (Hom.zeroInclusion (Hom.pullbackToUnit aU v) ≫ v ≫ g)
        (by
          have hp : p ≫ X.hom = (v ≫ g) ≫ Y.hom := by
            rw [Category.assoc, ← hb, ← Category.assoc, H.w,
              Category.assoc, MorphismProperty.Over.w]
          simpa only [Category.assoc] using
            congrArg (fun z => Hom.zeroInclusion (Hom.pullbackToUnit aU v) ≫ z) hp) := by
  let aU := Hom.pullbackToUnit a j
  let LU := pullbackLineBundle j L
  let : IsFinite (Hom.zeroInclusion aU ≫ (j ≫ q)) :=
    (boundaryFunctional_finite_flat T i q j L a hc).1
  let : Flat (Hom.zeroInclusion aU ≫ (j ≫ q)) :=
    (boundaryFunctional_finite_flat T i q j L a hc).2
  have : Smooth (j ≫ q) := SmoothOfRelativeDimension.smooth 1 (j ≫ q)
  have : Smooth ((j ≫ q) ≫ T.hom) := inferInstance
  have : IsSeparated ((j ≫ q) ≫ T.hom) := inferInstance
  have : QuasiCompact ((j ≫ q) ≫ T.hom) := inferInstance
  exact ZeroSectionFlatBaseChange.graph_zeroSection (j ≫ q) g hb α v p H LU aU

end Motivic.Cor
