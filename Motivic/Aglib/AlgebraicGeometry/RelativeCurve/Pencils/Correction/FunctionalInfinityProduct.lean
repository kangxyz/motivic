/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.FunctionalGraphRatioBoundary
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.FunctionalChartInfinityNorm
/-! # The original functional product on the entire infinity boundary

Both values follow from the original prescribed pairs and genuine maps into the
full infinity schemes. The source norm uses the complete inverse-infinity
fiber. No reduced support, normalized scalar, or residual freeness is used.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.FunctionalInfinityProduct`.

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

variable {S X A Z P DA : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) [IsSeparated π] (jA : X ⟶ P) [IsOpenImmersion jA]
  [SmoothOfRelativeDimension 1 (jA ≫ π)] (hA : jA ≫ π = q)
  (a : A ⟶ X) [Flat a] (z : Z ⟶ X)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z))
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

include hpairA ha in
/-- The original target functional quotient is one along every actual full
common-infinity map, by its original prescribed graph-pair equation. -/
theorem correctionFunctionalTarget_infinity_value
    {W Q : Scheme.{u}} (wA : W ⟶ pullback (jA ≫ π) π) (r : Q ⟶ W)
    (i : Q ⟶ commonInfinity π jA a dA)
    (hr : r ≫ wA = (i ≫ coprod.inl) ≫ commonBoundaryToLambda π jA a z dA ≫
      coprod.desc (Hom.infinityProductMap π jA dA) (Hom.graphBoundaryRestriction π jA z))
    [IsIso (pullbackUnitMap wA (sectionDualFunctional _
      (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)))
      (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
        (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA)))] :
    let L := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
    let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
      (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
    r.appTop (Modules.Hom.app
      (inv (pullbackUnitMap wA (sectionDualFunctional _ L cA)) ≫
        pullbackUnitMap wA (sectionDualFunctional _ L aA)) ⊤ (1 : Γ(W, ⊤))) = 1 := by
  let v : Q ⟶ commonBoundary π jA a z dA := i ≫ coprod.inl
  let θ := Hom.unitEndomorphismPullback
    (commonBoundaryToPsi q π jA (𝟙 X) (by simpa using hA)
      a a (𝟙 A) (by simp) z z (by simp) dA)
    (fixedProductBoundaryFrame q π a z e ha dA).hom
  obtain ⟨hθ, htarget⟩ := commonFunctionalGraphRatio_boundary_inverse
    q π jA (𝟙 X) (by simpa using hA) a a (𝟙 A) (by simp)
    z z (by simp) (IsPullback.id_vert z) e ha dA hdA LA aA bA hpairA wA r v hr
  let := hθ
  have hI : Hom.unitEndomorphismPullback
      (coprod.inl : commonInfinity π jA a dA ⟶ commonBoundary π jA a z dA) θ = 𝟙 _ := by
    dsimp only [θ]
    rw [Hom.unitEndomorphismPullback_comp]
    simp only [commonBoundaryToPsi, coprod.inl_map]
    rw [← Hom.unitEndomorphismPullback_comp, fixedProductBoundaryFrame_inl]
    simp [Hom.unitEndomorphismPullback]
  have hcoordinate : Hom.unitEndomorphismPullback v θ = 𝟙 _ := by
    dsimp only [v]
    rw [← Hom.unitEndomorphismPullback_comp, hI]
    simp [Hom.unitEndomorphismPullback]
  have hinverse : Hom.unitEndomorphismPullback v (inv θ) = 𝟙 _ := by
    have hc : Hom.unitEndomorphismPullback v (inv θ) ≫
        Hom.unitEndomorphismPullback v θ = 𝟙 _ := by
      simp only [Hom.unitEndomorphismPullback, Functor.map_inv, Category.assoc,
        Iso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc, Iso.inv_hom_id]
    simpa only [hcoordinate, Category.comp_id] using hc
  dsimp only
  rw [← Hom.unitEndomorphismPullback_app_one, htarget, hinverse]
  rfl

variable {Y C D T : Scheme.{u}}
  (f : C ⟶ P) (jB : Y ⟶ C) (p : Y ⟶ X)
  (hq : jB ≫ (f ≫ π) = p ≫ q) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (d : D ⟶ C) (bI : pullback f dA ⟶ D) (hbI : bI ≫ d = pullback.fst f dA)
  (N : LineBundle (pullback (a ≫ q) (f ≫ π)))
  (nS dS : SheafOfModules.unit (pullback (a ≫ q) (f ≫ π)).ringCatSheaf ⟶ N.val)
  (hN : pullbackSectionMap (psiBoundaryInclusion q (f ≫ π) jB p hq a z s hs d) nS =
    (fixedProductBoundaryFrame q (f ≫ π) a z e ha d).hom ≫
      pullbackSectionMap (psiBoundaryInclusion q (f ≫ π) jB p hq a z s hs d) dS)
  {R Q : Type u} [CommRing R] [CommRing Q]
  (n : T ⟶ Spec (.of R)) [IsFinite n] (φ : R →+* Q)
  (u : T ⟶ C) (t : Spec (.of R) ⟶ P) (Hf : IsPullback u n f t)
  (τ : Spec (.of Q) ⟶ DA)
  (hτ : Spec.map (CommRingCat.ofHom φ) ≫ t = τ ≫ dA)
  (w : T ⟶ pullback (a ≫ q) (f ≫ π))
  (hw : w ≫ pullback.snd (a ≫ q) (f ≫ π) = u)
  [IsIso (pullbackUnitMap w (sectionDualFunctional _ N dS))]
  (wA : Spec (.of R) ⟶ pullback (jA ≫ π) π)
  (i : Spec (.of Q) ⟶ commonInfinity π jA a dA)
  (hr : Spec.map (CommRingCat.ofHom φ) ≫ wA =
    (i ≫ coprod.inl) ≫ commonBoundaryToLambda π jA a z dA ≫
      coprod.desc (Hom.infinityProductMap π jA dA) (Hom.graphBoundaryRestriction π jA z))
  [IsIso (pullbackUnitMap wA (sectionDualFunctional _
    (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)))
    (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
      (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA)))]

include hpairA hN hbI Hf hτ hr hw in
/-- The same original quotient-norm product is one on every full infinity chart.
Both scalar values are proved from the original pairs and actual boundary maps. -/
theorem correctionFunctionalChart_infinity_product_eq_one :
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
  have htarget := correctionFunctionalTarget_infinity_value q π jA hA a z e ha dA hdA
    LA aA bA hpairA wA (Spec.map (CommRingCat.ofHom φ)) i hr
  have hnorm := correctionFunctionalChart_norm_infinity_value
    q (f ≫ π) jB p hq a z s hs e ha d N nS dS hN
    f dA bI hbI n φ u t Hf τ hτ w hw
  let g : Γ(Spec (.of R), ⊤) := Modules.Hom.app
    (inv (pullbackUnitMap wA (sectionDualFunctional _
      (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)))
      (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
        (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA))) ≫
      pullbackUnitMap wA (sectionDualFunctional _
        (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)))
        aA)) ⊤ (1 : Γ(Spec (.of R), ⊤))
  change (Spec.map (CommRingCat.ofHom φ)).appTop g = 1 at htarget
  have hscalar : (Scheme.ΓSpecIso (.of Q)).hom
      ((Spec.map (CommRingCat.ofHom φ)).appTop g) = 1 :=
    (congrArg (fun x : Γ(Spec (.of Q), ⊤) => (Scheme.ΓSpecIso (.of Q)).hom x) htarget).trans
      (map_one (Scheme.ΓSpecIso (.of Q)).hom.hom)
  have hnat := congrArg (fun l : Γ(Spec (.of R), ⊤) ⟶ CommRingCat.of Q => l g)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  have hnat' : (Scheme.ΓSpecIso (.of Q)).hom ((Spec.map (CommRingCat.ofHom φ)).appTop g) =
      φ ((Scheme.ΓSpecIso (.of R)).hom g) := by
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using hnat
  rw [hnat'] at hscalar
  rw [map_mul, hnorm, mul_one]
  exact hscalar

end AlgebraicGeometry.Scheme.RelativeCurvePencil
