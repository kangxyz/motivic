/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.ZeroSectionFlat
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Endpoints
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.SignedProductEndpoints

/-! # Signed pencil endpoint from two actual Cartesian section diagrams -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open _root_.AlgebraicGeometry.Scheme.SmoothSite.PolynomialPencil

universe u
namespace Motivic.SignedPencilSourceEndpoints
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLine

variable {k : Type u} [Field k] {X T V Y : SmoothSite (Spec (.of k))}
  {C E D : Scheme.{u}}
  (qA : C ⟶ T.left) (rA : C ⟶ Y.left) (hA : qA ≫ T.hom = rA ≫ Y.hom)
  (qN : E ⟶ V.left) (rN : E ⟶ Y.left) (hN : qN ≫ V.hom = rN ≫ Y.hom)
  (α : X ⟶ T) (β : X ⟶ V) [Flat α.left] [Flat β.left]
  (jA : D ⟶ C) (jN : D ⟶ E) (p : D ⟶ X.left)
  (hsA : IsPullback jA p qA α.left) (hsN : IsPullback jN p qN β.left)
  (A B : LineBundle C) (N M : LineBundle E)
  (a : A.val ⟶ SheafOfModules.unit C.ringCatSheaf)
  (b : B.val ⟶ SheafOfModules.unit C.ringCatSheaf)
  (n : N.val ⟶ SheafOfModules.unit E.ringCatSheaf)
  (d : M.val ⟶ SheafOfModules.unit E.ringCatSheaf)
  [Mono a] [Mono b] [Mono n] [Mono d]
  [IsFinite (Hom.zeroInclusion a ≫ qA)] [Flat (Hom.zeroInclusion a ≫ qA)]
  [IsFinite (Hom.zeroInclusion b ≫ qA)] [Flat (Hom.zeroInclusion b ≫ qA)]
  [IsFinite (Hom.zeroInclusion n ≫ qN)] [Flat (Hom.zeroInclusion n ≫ qN)]
  [IsFinite (Hom.zeroInclusion d ≫ qN)] [Flat (Hom.zeroInclusion d ≫ qN)]

variable [Smooth (qA ≫ T.hom)] [IsSeparated (qA ≫ T.hom)] [QuasiCompact (qA ≫ T.hom)]
  [Smooth (qN ≫ V.hom)] [IsSeparated (qN ≫ V.hom)] [QuasiCompact (qN ≫ V.hom)]
  [Smooth (p ≫ X.hom)] [IsSeparated (p ≫ X.hom)] [QuasiCompact (p ≫ X.hom)]
  (g : D ⟶ Y.left) (hgA : jA ≫ rA = g) (hgN : jN ≫ rN = g)
  (h : p ≫ X.hom = g ≫ Y.hom)
  (L : LineBundle D) (a0 : L.val ⟶ SheafOfModules.unit D.ringCatSheaf)
  (e : L.val ≅ (tensorLineBundle D (pullbackLineBundle jA A) (pullbackLineBundle jN N)).val)
  [IsFinite (Hom.zeroInclusion
    (Hom.productSection (Hom.pullbackToUnit b jA) (Hom.pullbackToUnit d jN)) ≫ p)]
  [Flat (Hom.zeroInclusion
    (Hom.productSection (Hom.pullbackToUnit b jA) (Hom.pullbackToUnit d jN)) ≫ p)]
  [IsFinite (familySource p L a0
    (e.hom ≫ Hom.productSection (Hom.pullbackToUnit a jA) (Hom.pullbackToUnit n jN)))]
  [Flat (familySource p L a0
    (e.hom ≫ Hom.productSection (Hom.pullbackToUnit a jA) (Hom.pullbackToUnit n jN)))]

include hsA hsN hgA hgN in
/-- The actual one endpoint is the two original source graph pullbacks with
correction sign λ − ψ, where λ=Z(a)−Z(b) and ψ=Z(d)−Z(n). -/
theorem signed_one_source_graphs :
    (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X 1) ≫
      signedCorrespondence p L a0
        (e.hom ≫ Hom.productSection (Hom.pullbackToUnit a jA) (Hom.pullbackToUnit n jN))
        g h (Hom.productSection (Hom.pullbackToUnit b jA) (Hom.pullbackToUnit d jN)) =
      (Cor.graphFunctor k).map α ≫
        (Cor.ofFiniteFlatSpan (Hom.zeroInclusion a ≫ qA) (Hom.zeroInclusion a ≫ rA)
            (by simp only [Category.assoc, hA]) -
          Cor.ofFiniteFlatSpan (Hom.zeroInclusion b ≫ qA) (Hom.zeroInclusion b ≫ rA)
            (by simp only [Category.assoc, hA])) -
      (Cor.graphFunctor k).map β ≫
        (Cor.ofFiniteFlatSpan (Hom.zeroInclusion d ≫ qN) (Hom.zeroInclusion d ≫ rN)
            (by simp only [Category.assoc, hN]) -
          Cor.ofFiniteFlatSpan (Hom.zeroInclusion n ≫ qN) (Hom.zeroInclusion n ≫ rN)
            (by simp only [Category.assoc, hN])) := by
  let : Flat jA := MorphismProperty.of_isPullback hsA.flip (inferInstanceAs (Flat α.left))
  let : Flat jN := MorphismProperty.of_isPullback hsN.flip (inferInstanceAs (Flat β.left))
  let : A.val.IsLocallyFree := lineBundle_isLocallyFree C A
  let : Mono (Hom.pullbackToUnit a jA) := by
    dsimp only [Hom.pullbackToUnit]
    infer_instance
  let := (ZeroSectionFlatBaseChange.pulled_finite_flat qA α jA p hsA A a).1
  let := (ZeroSectionFlatBaseChange.pulled_finite_flat qA α jA p hsA A a).2
  let : B.val.IsLocallyFree := lineBundle_isLocallyFree C B
  let : Mono (Hom.pullbackToUnit b jA) := by
    dsimp only [Hom.pullbackToUnit]
    infer_instance
  let := (ZeroSectionFlatBaseChange.pulled_finite_flat qA α jA p hsA B b).1
  let := (ZeroSectionFlatBaseChange.pulled_finite_flat qA α jA p hsA B b).2
  let : N.val.IsLocallyFree := lineBundle_isLocallyFree E N
  let : Mono (Hom.pullbackToUnit n jN) := by
    dsimp only [Hom.pullbackToUnit]
    infer_instance
  let := (ZeroSectionFlatBaseChange.pulled_finite_flat qN β jN p hsN N n).1
  let := (ZeroSectionFlatBaseChange.pulled_finite_flat qN β jN p hsN N n).2
  let : M.val.IsLocallyFree := lineBundle_isLocallyFree E M
  let : Mono (Hom.pullbackToUnit d jN) := by
    dsimp only [Hom.pullbackToUnit]
    infer_instance
  let := (ZeroSectionFlatBaseChange.pulled_finite_flat qN β jN p hsN M d).1
  let := (ZeroSectionFlatBaseChange.pulled_finite_flat qN β jN p hsN M d).2
  rw [← Endpoints.endpointMorphism_eq_a1Section,
    signed_one_four_sections p L (pullbackLineBundle jA A) (pullbackLineBundle jN N)
      (pullbackLineBundle jA B) (pullbackLineBundle jN M) a0
      (Hom.pullbackToUnit a jA) (Hom.pullbackToUnit n jN)
      (Hom.pullbackToUnit b jA) (Hom.pullbackToUnit d jN) e g h,
    Preadditive.comp_sub, Preadditive.comp_sub]
  have ha := ZeroSectionFlatBaseChange.graph_zeroSection qA rA hA
    α jA p hsA A a
  simp only [hgA] at ha
  have hb := ZeroSectionFlatBaseChange.graph_zeroSection qA rA hA
    α jA p hsA B b
  simp only [hgA] at hb
  have hn := ZeroSectionFlatBaseChange.graph_zeroSection qN rN hN
    β jN p hsN N n
  simp only [hgN] at hn
  have hd := ZeroSectionFlatBaseChange.graph_zeroSection qN rN hN
    β jN p hsN M d
  simp only [hgN] at hd
  rw [ha, hb, hd, hn]

end Motivic.SignedPencilSourceEndpoints
