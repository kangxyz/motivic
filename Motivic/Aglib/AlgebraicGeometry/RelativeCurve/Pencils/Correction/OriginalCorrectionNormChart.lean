/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormMarkedChart
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.FunctionalMarkedProduct
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.FunctionalInfinityProduct
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.MarkedChartSquare
/-! # The correction product on actual original marked charts

The original finite product map and a test into its full marked boundary
construct all chart and marked-section maps used by the norm computation.
This is a chart calculation, not a claim of completed global normalization.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalCorrectionNormChart`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Correction.NormalizedUnit`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S X Y A Z C P D DA : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) [IsSeparated π] (f : C ⟶ P) [IsFinite f]
  (jB : Y ⟶ C) [IsOpenImmersion jB] (jA : X ⟶ P) [IsOpenImmersion jA]
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
    let zA :=
      coprod.desc (Hom.infinityProductMap π jA dA) (Hom.graphBoundaryRestriction π jA z)
    pullbackSectionMap zA aA ≫ pullbackTensorMap zA LA.val
      (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)).val =
    tensorUnitSection (pullbackSectionMap zA bA)
      (Hom.relativeFullBoundaryFrame q π jA (𝟙 X) (hA.trans (Category.id_comp q).symm)
        z z (Category.comp_id z) (IsPullback.id_vert z) e dA hdA).inv)
  [IsIso (pullbackSectionMap
    (coprod.desc (Hom.infinityProductMap π jA dA) (Hom.graphBoundaryRestriction π jA z)) aA)]
  (H : IsPullback s (𝟙 Z) (jB ≫ f) (z ≫ jA))

include hret hpairA hN hbE H in
/-- Every affine test of the actual full marked boundary has product value one.
The local maps and full marked pullback square are outputs of the construction,
not independently supplied normalized chart data. -/
theorem originalCorrectionNormChart_marked_product_eq_one
    {R Q : Type u} [CommRing R] [CommRing Q]
    (w : Spec (.of R) ⟶ pullback (a ≫ q) π)
    (ε : Spec (.of Q) ⟶ pullback (normMarkedProductMap π (a ≫ q) (z ≫ jA)) w)
    [IsIso (pullbackUnitMap (pullback.fst (normProductMap π f (a ≫ q)) w)
      (sectionDualFunctional _ N dS))]
    [IsIso (pullbackUnitMap
      (w ≫ retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm))
      (sectionDualFunctional _
        (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)))
        (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
          (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA)))] :
    let F := normProductMap π f (a ≫ q)
    let τ := retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm)
    let L := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
    let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
      (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
    let g : R := (Scheme.ΓSpecIso (.of R)).hom (Modules.Hom.app
      (inv (pullbackUnitMap (w ≫ τ) (sectionDualFunctional _ L cA)) ≫
        pullbackUnitMap (w ≫ τ) (sectionDualFunctional _ L aA)) ⊤
        (1 : Γ(Spec (.of R), ⊤)))
    let b : Γ(pullback F w, ⊤) := Modules.Hom.app
      (inv (pullbackUnitMap (pullback.fst F w) (sectionDualFunctional _ N dS)) ≫
        pullbackUnitMap (pullback.fst F w) (sectionDualFunctional _ N nS)) ⊤
          (1 : Γ(pullback F w, ⊤))
    let φ := (Spec.preimage (normChartMarkedBase π (a ≫ q) (z ≫ jA) w ε)).hom
    let : Algebra R Γ(pullback F w, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F w)).toAlgebra
    ∀ [Module.Free R Γ(pullback F w, ⊤)], φ (g * Algebra.norm R b) = 1 := by
  let F := normProductMap π f (a ≫ q)
  let u := normChartSourceMap π f (a ≫ q) w
  let k := pullback.fst u jB
  let σ := normChartMarkedSection π f (a ≫ q) jB (z ≫ jA) s H w ε
  let m := normChartMarkedPoint π (a ≫ q) (z ≫ jA) w ε
  let z' := normChartMarkedBase π (a ≫ q) (z ≫ jA) w ε
  let φ := (Spec.preimage z').hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = z' := Spec.map_preimage z'
  let : Algebra R Γ(pullback F w, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F w)).toAlgebra
  dsimp only
  intro hfree
  let := hfree
  have hn : (σ ≫ k) ≫ pullback.snd F w = Spec.map (CommRingCat.ofHom φ) := by
    rw [hφ]
    exact normChartMarkedSection_base π f (a ≫ q) jB (z ≫ jA) s H w ε
  have HN : IsPullback σ (𝟙 _) (k ≫ pullback.snd F w)
      (Spec.map (CommRingCat.ofHom φ)) := by
    rw [hφ]
    exact normChartMarkedSection_isPullback π f (a ≫ q) jB (z ≫ jA) s H w ε
  have hz : Spec.map (CommRingCat.ofHom φ) ≫ (w ≫ pullback.snd (a ≫ q) π) =
      m ≫ (z ≫ jA) := by
    rw [hφ]
    exact normChartMarkedPoint_base π (a ≫ q) (z ≫ jA) w ε
  have hr : Spec.map (CommRingCat.ofHom φ) ≫
      (w ≫ retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm)) =
      correctionMarkedTargetAmbient q π f jA hA a k σ u (pullback.fst F w) rfl := by
    rw [hφ]
    exact originalNormChartMarked_target_ambient q π f jA hA a jB (z ≫ jA) s H w ε
  exact correctionFunctionalChart_marked_product_eq_one q π f jB jA p hq hret hA
    a z s hs hsK e ha d bE hbE N nS dS hN dA hdA LA aA bA hpairA
    (pullback.snd F w) φ k σ hn HN u (w ≫ pullback.snd (a ≫ q) π)
    (normChartSourceMap_isPullback π f (a ≫ q) w) m hz
    (normChartMarkedSection_original π f (a ≫ q) jB (z ≫ jA) s H w ε)
    (pullback.fst F w) rfl
    (w ≫ retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm)) hr

include hpairA hN in
omit [IsOpenImmersion jB] in
/-- The full original infinity test constructs the infinity chart factors and
forces the same literal quotient-norm product to equal one. -/
theorem originalCorrectionNormChart_infinity_product_eq_one
    (bI : pullback f dA ⟶ D) (hbI : bI ≫ d = pullback.fst f dA)
    {R Q : Type u} [CommRing R] [CommRing Q]
    (w : Spec (.of R) ⟶ pullback (a ≫ q) π)
    (ε : Spec (.of Q) ⟶ pullback (normMarkedProductMap π (a ≫ q) dA) w)
    [IsIso (pullbackUnitMap (pullback.fst (normProductMap π f (a ≫ q)) w)
      (sectionDualFunctional _ N dS))]
    [IsIso (pullbackUnitMap
      (w ≫ retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm))
      (sectionDualFunctional _
        (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)))
        (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
          (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA)))] :
    let F := normProductMap π f (a ≫ q)
    let τ := retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm)
    let L := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
    let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
      (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
    let g : R := (Scheme.ΓSpecIso (.of R)).hom (Modules.Hom.app
      (inv (pullbackUnitMap (w ≫ τ) (sectionDualFunctional _ L cA)) ≫
        pullbackUnitMap (w ≫ τ) (sectionDualFunctional _ L aA)) ⊤
        (1 : Γ(Spec (.of R), ⊤)))
    let b : Γ(pullback F w, ⊤) := Modules.Hom.app
      (inv (pullbackUnitMap (pullback.fst F w) (sectionDualFunctional _ N dS)) ≫
        pullbackUnitMap (pullback.fst F w) (sectionDualFunctional _ N nS)) ⊤
          (1 : Γ(pullback F w, ⊤))
    let φ := (Spec.preimage (normChartMarkedBase π (a ≫ q) dA w ε)).hom
    let : Algebra R Γ(pullback F w, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F w)).toAlgebra
    ∀ [Module.Free R Γ(pullback F w, ⊤)], φ (g * Algebra.norm R b) = 1 := by
  subst q
  let F := normProductMap π f (a ≫ (jA ≫ π))
  let u := normChartSourceMap π f (a ≫ (jA ≫ π)) w
  let z' := normChartMarkedBase π (a ≫ (jA ≫ π)) dA w ε
  let τ := normChartMarkedPoint π (a ≫ (jA ≫ π)) dA w ε
  let φ := (Spec.preimage z').hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = z' := Spec.map_preimage z'
  have hτ : z' ≫ (w ≫ pullback.snd (a ≫ (jA ≫ π)) π) = τ ≫ dA :=
    normChartMarkedPoint_base π (a ≫ (jA ≫ π)) dA w ε
  let i : Spec (.of Q) ⟶ commonInfinity π jA a dA :=
    pullback.lift (z' ≫ w) τ (by simpa only [Category.assoc] using hτ)
  have hr : Spec.map (CommRingCat.ofHom φ) ≫
      (w ≫ retainedNormParameterMap π (a ≫ (jA ≫ π)) jA a rfl) =
      (i ≫ coprod.inl) ≫ commonBoundaryToLambda π jA a z dA ≫
        coprod.desc (Hom.infinityProductMap π jA dA) (Hom.graphBoundaryRestriction π jA z) := by
    rw [hφ, commonBoundaryToLambda_inclusion]
    simp only [Category.assoc, commonBoundaryInclusion, coprod.inl_desc_assoc]
    change z' ≫ w ≫ retainedNormParameterMap π (a ≫ (jA ≫ π)) jA a rfl =
      i ≫ pullback.fst (pullback.snd (a ≫ (jA ≫ π)) π) dA ≫ commonToLambda π jA a
    dsimp only [i]
    rw [pullback.lift_fst_assoc]
    rfl
  let : Algebra R Γ(pullback F w, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F w)).toAlgebra
  dsimp only
  intro hfree
  let := hfree
  exact correctionFunctionalChart_infinity_product_eq_one (jA ≫ π) π jA rfl a z e ha
    dA hdA LA aA bA hpairA f jB p hq s hs d bI hbI N nS dS hN
    (pullback.snd F w) φ u (w ≫ pullback.snd (a ≫ (jA ≫ π)) π)
    (normChartSourceMap_isPullback π f (a ≫ (jA ≫ π)) w) τ
    (by rw [hφ]; exact hτ) (pullback.fst F w) rfl
    (w ≫ retainedNormParameterMap π (a ≫ (jA ≫ π)) jA a rfl) i hr

include hret hpairA hN hbE H in
/-- The actual full marked fiber has product value one in its own section ring.
Its canonical affine coordinates retain every nilpotent. -/
theorem originalCorrectionNormChart_marked_fiber_eq_one
    [IsAffineHom (z ≫ jA)]
    {R : Type u} [CommRing R]
    (w : Spec (.of R) ⟶ pullback (a ≫ q) π)
    [IsIso (pullbackUnitMap (pullback.fst (normProductMap π f (a ≫ q)) w)
      (sectionDualFunctional _ N dS))]
    [IsIso (pullbackUnitMap
      (w ≫ retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm))
      (sectionDualFunctional _
        (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)))
        (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
          (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA)))] :
    let F := normProductMap π f (a ≫ q)
    let τ := retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm)
    let L := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
    let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
      (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
    let g : R := (Scheme.ΓSpecIso (.of R)).hom (Modules.Hom.app
      (inv (pullbackUnitMap (w ≫ τ) (sectionDualFunctional _ L cA)) ≫
        pullbackUnitMap (w ≫ τ) (sectionDualFunctional _ L aA)) ⊤
        (1 : Γ(Spec (.of R), ⊤)))
    let b : Γ(pullback F w, ⊤) := Modules.Hom.app
      (inv (pullbackUnitMap (pullback.fst F w) (sectionDualFunctional _ N dS)) ≫
        pullbackUnitMap (pullback.fst F w) (sectionDualFunctional _ N nS)) ⊤
          (1 : Γ(pullback F w, ⊤))
    let φ := FiniteSchemeNormBaseChange.scalarMap
      (pullback.snd (normMarkedProductMap π (a ≫ q) (z ≫ jA)) w)
    let : Algebra R Γ(pullback F w, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F w)).toAlgebra
    ∀ [Module.Free R Γ(pullback F w, ⊤)], φ (g * Algebra.norm R b) = 1 := by
  let F := normProductMap π f (a ≫ q)
  let z' := normMarkedProductMap π (a ≫ q) (z ≫ jA)
  let : IsAffineHom z' :=
    MorphismProperty.of_isPullback
      (retainedProductInclusion_isPullback (a ≫ q) π (z ≫ jA)) inferInstance
  let : IsAffine (pullback z' w) := isAffine_of_isAffineHom (pullback.snd z' w)
  let : Algebra R Γ(pullback F w, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F w)).toAlgebra
  dsimp only
  intro hfree
  let := hfree
  have hh := originalCorrectionNormChart_marked_product_eq_one q π f jB jA p hq hret hA
    a z s hs hsK e ha d bE hbE N nS dS hN dA hdA LA aA bA hpairA H w
    (pullback z' w).isoSpec.inv
  change (Spec.preimage ((pullback z' w).isoSpec.inv ≫ pullback.snd z' w)).hom _ = 1 at hh
  rw [← FiniteSchemeNormBaseChange.spec_scalarMap (pullback.snd z' w),
    Spec.preimage_map] at hh
  exact hh

include hpairA hN in
omit [IsOpenImmersion jB] in
/-- The original complete infinity fiber has value one in its own section ring. -/
theorem originalCorrectionNormChart_infinity_fiber_eq_one
    (bI : pullback f dA ⟶ D) (hbI : bI ≫ d = pullback.fst f dA)
    [IsAffineHom dA]
    {R : Type u} [CommRing R]
    (w : Spec (.of R) ⟶ pullback (a ≫ q) π)
    [IsIso (pullbackUnitMap (pullback.fst (normProductMap π f (a ≫ q)) w)
      (sectionDualFunctional _ N dS))]
    [IsIso (pullbackUnitMap
      (w ≫ retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm))
      (sectionDualFunctional _
        (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)))
        (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
          (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA)))] :
    let F := normProductMap π f (a ≫ q)
    let τ := retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm)
    let L := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
    let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
      (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
    let g : R := (Scheme.ΓSpecIso (.of R)).hom (Modules.Hom.app
      (inv (pullbackUnitMap (w ≫ τ) (sectionDualFunctional _ L cA)) ≫
        pullbackUnitMap (w ≫ τ) (sectionDualFunctional _ L aA)) ⊤
        (1 : Γ(Spec (.of R), ⊤)))
    let b : Γ(pullback F w, ⊤) := Modules.Hom.app
      (inv (pullbackUnitMap (pullback.fst F w) (sectionDualFunctional _ N dS)) ≫
        pullbackUnitMap (pullback.fst F w) (sectionDualFunctional _ N nS)) ⊤
          (1 : Γ(pullback F w, ⊤))
    let φ := FiniteSchemeNormBaseChange.scalarMap
      (pullback.snd (normMarkedProductMap π (a ≫ q) dA) w)
    let : Algebra R Γ(pullback F w, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F w)).toAlgebra
    ∀ [Module.Free R Γ(pullback F w, ⊤)], φ (g * Algebra.norm R b) = 1 := by
  let F := normProductMap π f (a ≫ q)
  let z' := normMarkedProductMap π (a ≫ q) dA
  let : IsAffineHom z' :=
    MorphismProperty.of_isPullback
      (retainedProductInclusion_isPullback (a ≫ q) π dA) inferInstance
  let : IsAffine (pullback z' w) := isAffine_of_isAffineHom (pullback.snd z' w)
  let : Algebra R Γ(pullback F w, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F w)).toAlgebra
  dsimp only
  intro hfree
  let := hfree
  have hh := originalCorrectionNormChart_infinity_product_eq_one q π f jB jA p hq hA
    a z s hs e ha d N nS dS hN dA hdA LA aA bA hpairA bI hbI w
    (pullback z' w).isoSpec.inv
  change (Spec.preimage ((pullback z' w).isoSpec.inv ≫ pullback.snd z' w)).hom _ = 1 at hh
  rw [← FiniteSchemeNormBaseChange.spec_scalarMap (pullback.snd z' w),
    Spec.preimage_map] at hh
  exact hh

end AlgebraicGeometry.Scheme.RelativeCurvePencil
