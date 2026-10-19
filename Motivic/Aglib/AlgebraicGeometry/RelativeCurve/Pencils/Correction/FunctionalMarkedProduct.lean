/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.FunctionalGraphRatioBoundary
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.FunctionalChartMarkedNorm
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.TargetMarkedCoordinate
/-! # The original functional product is one on the entire marked boundary

The target quotient and source norm come from the original prescribed pairs.
Their common coordinate is constructed from the same actual chart point over
the fixed disjoint parameter. Arbitrary boundary rings, their nilpotents, and
the entire residual scheme are retained; only the total source chart is free.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.FunctionalMarkedProduct`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Correction.OriginalCorrectionNormChart`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

private theorem unitEndomorphismPullback_inv_app_mul
    {X Q : Scheme.{u}} (v : Q ⟶ X)
    (θ : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsIso θ] :
    (show Γ(Q, ⊤) from Modules.Hom.app (Hom.unitEndomorphismPullback v (inv θ)) ⊤
      (1 : Γ(Q, ⊤))) *
      (show Γ(Q, ⊤) from Modules.Hom.app (Hom.unitEndomorphismPullback v θ) ⊤
        (1 : Γ(Q, ⊤))) = 1 := by
  let x : Γ(Q, ⊤) := Modules.Hom.app (Hom.unitEndomorphismPullback v (inv θ)) ⊤
    (1 : Γ(Q, ⊤))
  let y : Γ(Q, ⊤) := Modules.Hom.app (Hom.unitEndomorphismPullback v θ) ⊤ (1 : Γ(Q, ⊤))
  change x * y = 1
  have hc : Hom.unitEndomorphismPullback v (inv θ) ≫
      Hom.unitEndomorphismPullback v θ = 𝟙 _ := by
    simp only [Hom.unitEndomorphismPullback, Functor.map_inv, Category.assoc,
      Iso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc, Iso.inv_hom_id]
  have he := congrArg (fun l : SheafOfModules.unit Q.ringCatSheaf ⟶
      SheafOfModules.unit Q.ringCatSheaf =>
        (show Γ(Q, ⊤) from Modules.Hom.app l ⊤ (1 : Γ(Q, ⊤)))) hc
  change (show Γ(Q, ⊤) from Modules.Hom.app (Hom.unitEndomorphismPullback v θ) ⊤ x) = 1 at he
  have hl : (show Γ(Q, ⊤) from Modules.Hom.app (Hom.unitEndomorphismPullback v θ) ⊤ x) =
      x * y := by
    have h := Modules.Hom.app_smul (X := Q) (U := ⊤)
      (Hom.unitEndomorphismPullback v θ) x (1 : Γ(Q, ⊤))
    change (show Γ(Q, ⊤) from Modules.Hom.app (Hom.unitEndomorphismPullback v θ) ⊤
      (x * 1 : Γ(Q, ⊤))) = x * y at h
    simpa only [mul_one] using h
  exact hl.symm.trans he

section MarkedGeometry

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

/-- The fixed parameter and original marked chart give the actual common marked point. -/
def correctionChartCommonMarkedFactor : Q ⟶ commonZero π jA a z :=
  let μ := correctionChartMarkedFactor q (f ≫ π) jB p hq a z s hs k σ u m hj w hw
  pullback.lift (μ ≫ pullback.fst (a ≫ q) (z ≫ q))
    (μ ≫ pullback.snd (a ≫ q) (z ≫ q)) (by
      simpa only [commonProjection, Category.assoc, hA] using
        congrArg (fun l => μ ≫ l) (pullback.condition (f := a ≫ q) (g := z ≫ q)))

/-- Its native target factor is the factor constructed from the same original chart. -/
theorem correctionChartCommonMarkedFactor_toNative :
    correctionChartCommonMarkedFactor q π f jB jA p hq hA a z s hs k σ u m hj w hw ≫
      commonZeroToLambda π jA a z =
    correctionNativeTargetMarkedFactor q π f jB jA p hret hA a z s hs
      k σ u m hj w hw := by
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
  apply pullback.hom_ext
  · rw [hparameter]
    simp [correctionChartCommonMarkedFactor, commonZeroToLambda,
      correctionMarkedTargetAmbient, correctionChartMarkedFactor]
  · simp [correctionChartCommonMarkedFactor, commonZeroToLambda,
      correctionNativeTargetMarkedFactor, correctionChartMarkedFactor]

include hret in
/-- The common-boundary factor lies over the literal original target ambient point. -/
theorem correctionChartCommonMarkedFactor_ambient {D : Scheme.{u}} (d : D ⟶ P) :
    (correctionChartCommonMarkedFactor q π f jB jA p hq hA a z s hs k σ u m hj w hw ≫
      coprod.inr) ≫ commonBoundaryToLambda π jA a z d ≫
        coprod.desc (Hom.infinityProductMap π jA d) (Hom.graphBoundaryRestriction π jA z) =
      correctionMarkedTargetAmbient q π f jA hA a k σ u w hw := by
  simp only [commonBoundaryToLambda, Category.assoc, coprod.inr_map_assoc,
    coprod.inr_desc]
  rw [← Category.assoc,
    correctionChartCommonMarkedFactor_toNative q π f jB jA p hq hret hA]
  exact (Hom.graphBoundaryRestriction_isPullback π jA z).lift_fst _ _ _

variable [IsSeparated q] [SmoothOfRelativeDimension 1 q] [IsSeparated π]
  [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)] [Flat a]
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z))
  {DA WA : Scheme.{u}} (dA : DA ⟶ P) (hdA : Disjoint (Set.range jA) (Set.range dA))
  (LA : LineBundle (pullback (jA ≫ π) π))
  (aA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))).val)
  (bA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶ LA.val)
  (hpairA :
    let zA := coprod.desc (Hom.infinityProductMap π jA dA) (Hom.graphBoundaryRestriction π jA z)
    pullbackSectionMap zA aA ≫ pullbackTensorMap zA LA.val
      (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)).val =
    tensorUnitSection (pullbackSectionMap zA bA)
      (Hom.relativeFullBoundaryFrame q π jA (𝟙 X) (hA.trans (Category.id_comp q).symm)
        z z (Category.comp_id z) (IsPullback.id_vert z) e dA hdA).inv)
  [IsIso (pullbackSectionMap
    (coprod.desc (Hom.infinityProductMap π jA dA) (Hom.graphBoundaryRestriction π jA z)) aA)]
  (wA : WA ⟶ pullback (jA ≫ π) π) (r : Q ⟶ WA)
  (hr : r ≫ wA = correctionMarkedTargetAmbient q π f jA hA a k σ u w hw)
  [IsIso (pullbackUnitMap wA (sectionDualFunctional _
    (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)))
    (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
      (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA)))]

include hpairA hr hret ha in
/-- The original target quotient is inverse to the SAME correction marked coordinate.
The equality holds on the whole marked test scheme, not just its residue fields. -/
theorem correctionFunctionalTarget_marked_mul_coordinate :
    let L := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
    let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
      (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
    let g : Γ(WA, ⊤) := Modules.Hom.app
      (inv (pullbackUnitMap wA (sectionDualFunctional _ L cA)) ≫
        pullbackUnitMap wA (sectionDualFunctional _ L aA)) ⊤ (1 : Γ(WA, ⊤))
    let μ := correctionChartMarkedFactor q (f ≫ π) jB p hq a z s hs k σ u m hj w hw
    r.appTop g * (show Γ(Q, ⊤) from Modules.Hom.app (Hom.unitEndomorphismPullback
      (μ ≫ Hom.boundaryProductMap q a z)
      (e.hom ≫ Hom.idealInclusion (Hom.boundaryGraphTarget q z))) ⊤ (1 : Γ(Q, ⊤))) = 1 := by
  let ν := correctionChartCommonMarkedFactor q π f jB jA p hq hA a z s hs k σ u m hj w hw
  let v : Q ⟶ commonBoundary π jA a z dA := ν ≫ coprod.inr
  let θ := Hom.unitEndomorphismPullback
    (commonBoundaryToPsi q π jA (𝟙 X) (by simpa using hA)
      a a (𝟙 A) (by simp) z z (by simp) dA)
    (fixedProductBoundaryFrame q π a z e ha dA).hom
  obtain ⟨hθ, htarget⟩ := commonFunctionalGraphRatio_boundary_inverse
    q π jA (𝟙 X) (by simpa using hA) a a (𝟙 A) (by simp)
    z z (by simp) (IsPullback.id_vert z) e ha dA hdA LA aA bA hpairA wA r v
    (hr.trans (correctionChartCommonMarkedFactor_ambient
      q π f jB jA p hq hret hA a z s hs k σ u m hj w hw dA).symm)
  let := hθ
  have hcoordinate : Hom.unitEndomorphismPullback v θ =
      Hom.unitEndomorphismPullback
        (correctionChartMarkedFactor q (f ≫ π) jB p hq a z s hs k σ u m hj w hw ≫
          Hom.boundaryProductMap q a z)
        (e.hom ≫ Hom.idealInclusion (Hom.boundaryGraphTarget q z)) := by
    have hmaps : (ν ≫ commonZeroToLambda π jA a z) ≫
        (Hom.relativeBoundaryProductIso q π jA (𝟙 X) (by simpa using hA)
          z z (by simp)).hom ≫ Hom.boundaryProductMap q (𝟙 X) z =
        correctionChartMarkedFactor q (f ≫ π) jB p hq a z s hs k σ u m hj w hw ≫
          Hom.boundaryProductMap q a z := by
      rw [correctionChartCommonMarkedFactor_toNative q π f jB jA p hq hret hA]
      exact (correctionChart_targetMarked_coordinate_eq
        q π f jB jA p hq hret hA a z s hs k σ u m hj w hw).symm
    calc
      Hom.unitEndomorphismPullback v θ =
          Hom.unitEndomorphismPullback (ν ≫ commonZeroToLambda π jA a z)
            (Hom.unitEndomorphismPullback coprod.inr
              (Hom.relativeFullBoundaryCoordinate q π jA (𝟙 X) (by simpa using hA)
                z z (by simp) (IsPullback.id_vert z) e dA hdA)) := by
        dsimp only [θ]
        rw [← commonBoundary_coordinate_eq q π a z e ha dA jA (𝟙 X)
          (by simpa using hA) a (𝟙 A) (by simp) z (by simp) (IsPullback.id_vert z) hdA]
        simp only [Hom.unitEndomorphismPullback_comp, v, commonBoundaryToLambda,
          Category.assoc, coprod.inr_map]
      _ = Hom.unitEndomorphismPullback
          ((ν ≫ commonZeroToLambda π jA a z) ≫
            (Hom.relativeBoundaryProductIso q π jA (𝟙 X) (by simpa using hA)
              z z (by simp)).hom ≫ Hom.boundaryProductMap q (𝟙 X) z)
          (e.hom ≫ Hom.idealInclusion (Hom.boundaryGraphTarget q z)) := by
        rw [Hom.relativeFullBoundaryCoordinate_inr, Hom.unitEndomorphismPullback_comp]
      _ = _ := congrArg (fun l => Hom.unitEndomorphismPullback l
        (e.hom ≫ Hom.idealInclusion (Hom.boundaryGraphTarget q z))) hmaps
  dsimp only
  rw [← Hom.unitEndomorphismPullback_app_one, htarget, ← hcoordinate]
  exact unitEndomorphismPullback_inv_app_mul v θ

end MarkedGeometry

section NormProduct

variable {S X Y A Z C P D DA T V : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) [IsSeparated π] (f : C ⟶ P) [IsFinite f]
  (jB : Y ⟶ C) (jA : X ⟶ P) [IsOpenImmersion jA]
  [SmoothOfRelativeDimension 1 (jA ≫ π)] (p : Y ⟶ X)
  (hq : jB ≫ (f ≫ π) = p ≫ q)
  (hret : jB ≫ f = p ≫ jA) (hA : jA ≫ π = q)
  (a : A ⟶ X) [Flat a] (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (hsK : (s ≫ jB) ≫ f = z ≫ jA)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z))
  (d : D ⟶ C)
  (bE : (Scheme.residualMarkedFiberOpen f jB (z ≫ jA) s hsK).toScheme ⟶ D)
  (hbE : bE ≫ d = Scheme.residualMarkedFiberMap f jB (z ≫ jA) s hsK)
  (N : LineBundle (pullback (a ≫ q) (f ≫ π)))
  (nS dS : SheafOfModules.unit (pullback (a ≫ q) (f ≫ π)).ringCatSheaf ⟶ N.val)
  (hN : pullbackSectionMap (psiBoundaryInclusion q (f ≫ π) jB p hq a z s hs d) nS =
    (fixedProductBoundaryFrame q (f ≫ π) a z e ha d).hom ≫
      pullbackSectionMap (psiBoundaryInclusion q (f ≫ π) jB p hq a z s hs d) dS)
  (dA : DA ⟶ P) (hdA : Disjoint (Set.range jA) (Set.range dA))
  (LA : LineBundle (pullback (jA ≫ π) π))
  (aA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))).val)
  (bA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶ LA.val)
  (hpairA :
    let zA := coprod.desc (Hom.infinityProductMap π jA dA) (Hom.graphBoundaryRestriction π jA z)
    pullbackSectionMap zA aA ≫ pullbackTensorMap zA LA.val
      (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)).val =
    tensorUnitSection (pullbackSectionMap zA bA)
      (Hom.relativeFullBoundaryFrame q π jA (𝟙 X) (hA.trans (Category.id_comp q).symm)
        z z (Category.comp_id z) (IsPullback.id_vert z) e dA hdA).inv)
  [IsIso (pullbackSectionMap
    (coprod.desc (Hom.infinityProductMap π jA dA) (Hom.graphBoundaryRestriction π jA z)) aA)]
  {R Q : Type u} [CommRing R] [CommRing Q]
  (n : T ⟶ Spec (.of R)) [IsFinite n] (φ : R →+* Q)
  (k : V ⟶ T) [IsOpenImmersion k] (σ : Spec (.of Q) ⟶ V)
  (hn : (σ ≫ k) ≫ n = Spec.map (CommRingCat.ofHom φ))
  (HN : IsPullback σ (𝟙 _) (k ≫ n) (Spec.map (CommRingCat.ofHom φ)))
  (u : T ⟶ C) (t : Spec (.of R) ⟶ P) (Hf : IsPullback u n f t)
  (m : Spec (.of Q) ⟶ Z)
  (hz : Spec.map (CommRingCat.ofHom φ) ≫ t = m ≫ (z ≫ jA))
  (hj : m ≫ (s ≫ jB) = (σ ≫ k) ≫ u)
  (w : T ⟶ pullback (a ≫ q) (f ≫ π))
  (hw : w ≫ pullback.snd (a ≫ q) (f ≫ π) = u)
  [IsIso (pullbackUnitMap w (sectionDualFunctional _ N dS))]
  (wA : Spec (.of R) ⟶ pullback (jA ≫ π) π)
  (hr : Spec.map (CommRingCat.ofHom φ) ≫ wA =
    correctionMarkedTargetAmbient q π f jA hA a k σ u w hw)
  [IsIso (pullbackUnitMap wA (sectionDualFunctional _
    (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)))
    (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
      (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA)))]

include hret hpairA hN hbE hn HN Hf hz hr hj in
/-- The actual original target quotient times the source determinant norm is one
under every genuine marked base change. The target ambient equality concerns
only original scheme maps; no normalized unit, value, or germ is supplied. -/
theorem correctionFunctionalChart_marked_product_eq_one :
    let L := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
    let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
      (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
    let g : R := (Scheme.ΓSpecIso (.of R)).hom (Modules.Hom.app
      (inv (pullbackUnitMap wA (sectionDualFunctional _ L cA)) ≫
        pullbackUnitMap wA (sectionDualFunctional _ L aA)) ⊤ (1 : Γ(Spec (.of R), ⊤)))
    let b : Γ(T, ⊤) := Modules.Hom.app
      (inv (pullbackUnitMap w (sectionDualFunctional _ N dS)) ≫
        pullbackUnitMap w (sectionDualFunctional _ N nS)) ⊤ (1 : Γ(T, ⊤))
    let : Algebra R Γ(T, ⊤) := (FiniteSchemeNormBaseChange.scalarMap n).toAlgebra
    ∀ [Module.Free R Γ(T, ⊤)], φ (g * Algebra.norm R b) = 1 := by
  let : Algebra R Γ(T, ⊤) := (FiniteSchemeNormBaseChange.scalarMap n).toAlgebra
  dsimp only
  intro hfree
  let := hfree
  have htarget := correctionFunctionalTarget_marked_mul_coordinate
    q π f jB jA p hq hret hA a z s hs k σ u m hj w hw e ha dA hdA
    LA aA bA hpairA wA (Spec.map (CommRingCat.ofHom φ)) hr
  have hnorm := correctionFunctionalChart_norm_marked_value
    (q := q) (π := f ≫ π) (j := jB) (p := p) (hq := hq) (a := a)
    (z := z) (s := s) (hs := hs) (u := u) (w := w) (hw := hw)
    (f := f) (zK := z ≫ jA) (hsK := hsK) (d := d) (bE := bE) (hbE := hbE)
    e ha N nS dS hN n φ k σ hn HN t Hf m hz hj
  let g : Γ(Spec (.of R), ⊤) := Modules.Hom.app
    (inv (pullbackUnitMap wA (sectionDualFunctional _
      (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)))
      (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
        (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA))) ≫
      pullbackUnitMap wA (sectionDualFunctional _
        (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)))
        aA)) ⊤ (1 : Γ(Spec (.of R), ⊤))
  let c : Γ(Spec (.of Q), ⊤) := Modules.Hom.app (Hom.unitEndomorphismPullback
    (correctionChartMarkedFactor q (f ≫ π) jB p hq a z s hs k σ u m hj w hw ≫
      Hom.boundaryProductMap q a z)
    (e.hom ≫ Hom.idealInclusion (Hom.boundaryGraphTarget q z))) ⊤
      (1 : Γ(Spec (.of Q), ⊤))
  change (Spec.map (CommRingCat.ofHom φ)).appTop g * c = 1 at htarget
  have hscalar : (Scheme.ΓSpecIso (.of Q)).hom
      ((Spec.map (CommRingCat.ofHom φ)).appTop g) *
      (Scheme.ΓSpecIso (.of Q)).hom c = 1 := by
    calc
      _ = (Scheme.ΓSpecIso (.of Q)).hom
          ((Spec.map (CommRingCat.ofHom φ)).appTop g * c) :=
        (map_mul (Scheme.ΓSpecIso (.of Q)).hom.hom _ _).symm
      _ = (Scheme.ΓSpecIso (.of Q)).hom (1 : Γ(Spec (.of Q), ⊤)) :=
        congrArg (fun x : Γ(Spec (.of Q), ⊤) => (Scheme.ΓSpecIso (.of Q)).hom x) htarget
      _ = 1 := map_one (Scheme.ΓSpecIso (.of Q)).hom.hom
  have hnat := congrArg (fun l : Γ(Spec (.of R), ⊤) ⟶ CommRingCat.of Q => l g)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  have hnat' : (Scheme.ΓSpecIso (.of Q)).hom ((Spec.map (CommRingCat.ofHom φ)).appTop g) =
      φ ((Scheme.ΓSpecIso (.of R)).hom g) := by
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using hnat
  rw [hnat'] at hscalar
  rw [map_mul, hnorm]
  exact hscalar

end NormProduct

end AlgebraicGeometry.Scheme.RelativeCurvePencil
