/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Norm.SectionPairBoundaryEquality
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairNormIdeal
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.AffineMarkedGraphRegular
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberFactorizationRatio
/-! # The same original association unit on the full marked boundary

The source norm and target coefficient are computed from the original pairs.
Cancellation takes place in the actual marked ring, using its flat parameter
map. No reducedness, source domain, or closed-pullback Mono is used.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.SectionPairNormalizedUnit`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Norm.SectionPairNormNeighborhood`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S X Y Z C P D : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (π : P ⟶ S) [IsSeparated π]
  (f : C ⟶ P) [IsFinite f] (jB : Y ⟶ C) [IsOpenImmersion jB]
  [SmoothOfRelativeDimension 1 (jB ≫ f ≫ π)]
  (jA : X ⟶ P) [IsOpenImmersion jA]
  [SmoothOfRelativeDimension 1 (jA ≫ π)] (p : Y ⟶ X) [Flat p]
  (hret : jB ≫ f = p ≫ jA) (hA : jA ≫ π = q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget q z))
  (d : D ⟶ C) (hd : Disjoint (Set.range jB) (Set.range d))

variable (L : LineBundle (pullback (jB ≫ f ≫ π) (f ≫ π)))
  (aS : SheafOfModules.unit (pullback (jB ≫ f ≫ π) (f ≫ π)).ringCatSheaf ⟶
    (tensorLineBundle _ L (dualLineBundle _
      (relativeCompactificationGraphLine (f ≫ π) jB))).val)
  (bS : SheafOfModules.unit (pullback (jB ≫ f ≫ π) (f ≫ π)).ringCatSheaf ⟶ L.val)
  (hpair : pullbackSectionMap (fullBoundaryProductMap (f ≫ π) jB d s) aS ≫
      pullbackTensorMap (fullBoundaryProductMap (f ≫ π) jB d s) L.val
        (dualLineBundle _ (relativeCompactificationGraphLine (f ≫ π) jB)).val =
    tensorUnitSection (pullbackSectionMap (fullBoundaryProductMap (f ≫ π) jB d s) bS)
      (relativeFullBoundaryFrame q (f ≫ π) jB p
        (retained_source_structure q π f jB jA p hret hA) z s hs H e d hd).inv)

variable {R Q : Type u} [CommRing R] [CommRing Q] {T V : Scheme.{u}}
  (n : T ⟶ Spec (.of R)) [IsFinite n] (φ : R →+* Q)
  (k : V ⟶ T) [IsOpenImmersion k] (σ : Spec (.of Q) ⟶ V)
  (hn : (σ ≫ k) ≫ n = Spec.map (CommRingCat.ofHom φ))
  (HN : IsPullback σ (𝟙 _) (k ≫ n) (Spec.map (CommRingCat.ofHom φ)))
  (u : T ⟶ C) (t : Spec (.of R) ⟶ P) (Hf : IsPullback u n f t)
  (a : Spec (.of Q) ⟶ Z)
  (hz : Spec.map (CommRingCat.ofHom φ) ≫ t = a ≫ (z ≫ jA))
  (hj : a ≫ (s ≫ jB) = (σ ≫ k) ≫ u)
  (w : T ⟶ pullback (jB ≫ f ≫ π) (f ≫ π))
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _ L bS) w)]
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _
    (tensorLineBundle _ L (dualLineBundle _
      (relativeCompactificationGraphLine (f ≫ π) jB))) aS) w)]
  (hw : w ≫ pullback.snd (jB ≫ f ≫ π) (f ≫ π) = u)
  (bE : (Scheme.residualMarkedFiberOpen f jB (z ≫ jA) s
    (retainedSectionPair_marked_map f jB jA p hret z s hs)).toScheme ⟶ D)
  (hbE : bE ≫ d = Scheme.residualMarkedFiberMap f jB (z ≫ jA) s
    (retainedSectionPair_marked_map f jB jA p hret z s hs))

variable {DA WA : Scheme.{u}}
  (dA : DA ⟶ P) (hdA : Disjoint (Set.range jA) (Set.range dA))
  (LA : LineBundle (pullback (jA ≫ π) π))
  (aA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine π jA))).val)
  (bA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶ LA.val)
  (hpairA : pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA ≫
      pullbackTensorMap (fullBoundaryProductMap π jA dA z) LA.val
        (dualLineBundle _ (relativeCompactificationGraphLine π jA)).val =
    tensorUnitSection (pullbackSectionMap (fullBoundaryProductMap π jA dA z) bA)
      (relativeFullBoundaryFrame q π jA (𝟙 X) (hA.trans (Category.id_comp q).symm)
        z z (Category.comp_id z) (IsPullback.id_vert z) e dA hdA).inv)
  (vA : WA ⟶ pullback (jA ≫ π) π)
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _ LA bA) vA)]
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _
    (tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine π jA))) aA) vA)]
  (wA : Spec (.of R) ⟶ pullback (jB ≫ f ≫ π) π)
  (hgraph : w ≫ graphProductMap π f jB = n ≫ wA)
  (l : Spec (.of R) ⟶ pullback (retainedParameterProductMap π f jB jA p hret) vA)
  (hl : l ≫ pullback.fst (retainedParameterProductMap π f jB jA p hret) vA = wA)

variable [IsOpenImmersion w]
  (Hz : IsPullback a (Spec.map (CommRingCat.ofHom φ)) (z ≫ jA) t)

include hpair hpairA hn HN Hf hz hbE hj hw hgraph hl Hz in
/-- Any unit satisfying the actual graph association equation is one on the
entire marked scheme. The same unit is used before and after restriction. -/
theorem sectionPairGraph_association_marked_eq_one :
    let cB : Γ(T, ⊤) := Modules.Hom.app
      (RelativeCurvePencil.sectionPairGraphCoefficient (f ≫ π) jB L aS bS w) ⊤
      (1 : Γ(T, ⊤))
    let cA : R := (Scheme.ΓSpecIso (.of R)).hom
      ((l ≫ pullback.snd (retainedParameterProductMap π f jB jA p hret) vA).appTop
        (Modules.Hom.app (RelativeCurvePencil.sectionPairGraphCoefficient π jA LA aA bA vA) ⊤
          (1 : Γ(WA, ⊤))))
    let : Algebra R Γ(T, ⊤) := (FiniteSchemeNormBaseChange.scalarMap n).toAlgebra
    ∀ [Module.Free R Γ(T, ⊤)] (μ : Rˣ),
      Algebra.norm R cB = (μ : R) * cA → φ (μ : R) = 1 := by
  dsimp only
  intro hfree μ hμ
  let : Algebra R Γ(T, ⊤) := (FiniteSchemeNormBaseChange.scalarMap n).toAlgebra
  let := hfree
  let α := Scheme.graphChartMarkedFactor (f ≫ π) jB s k σ u a hj w hw
  have : Flat α := Scheme.graphChartMarkedFactor_flat
    (f ≫ π) jB s f (z ≫ jA)
    (retainedSectionPair_marked_map f jB jA p hret z s hs)
    n k σ (Spec.map (CommRingCat.ofHom φ)) hn u t Hf a Hz hj w hw
  let m := α ≫ (relativeBoundaryProductIso q (f ≫ π) jB p
    (retained_source_structure q π f jB jA p hret hA) z s hs).hom ≫
      boundaryProductMap q p z
  let θ := e.hom ≫ idealInclusion (boundaryGraphTarget q z)
  have : Mono (idealInclusion (boundaryGraphTarget q z)) :=
    idealInclusionMono (boundaryGraphTarget q z)
  have : Mono θ := mono_comp _ _
  have hr := Modules.isSMulRegular_unitEnd_app_one_flat_pullback m θ
  rw [← unitEndomorphismPullback_app_one] at hr
  let c : Γ(Spec (.of Q), ⊤) :=
    Modules.Hom.app (unitEndomorphismPullback m θ) ⊤ (1 : Γ(Spec (.of Q), ⊤))
  have hrQ : IsSMulRegular Q ((Scheme.ΓSpecIso (.of Q)).hom c) := by
    intro x y hxy
    apply (Scheme.ΓSpecIso (.of Q)).commRingCatIsoToRingEquiv.symm.injective
    apply hr
    change c * (Scheme.ΓSpecIso (.of Q)).inv x =
      c * (Scheme.ΓSpecIso (.of Q)).inv y
    change (Scheme.ΓSpecIso (.of Q)).hom c * x =
      (Scheme.ΓSpecIso (.of Q)).hom c * y at hxy
    simpa only [map_mul, Iso.hom_inv_id_apply] using
      congrArg (Scheme.ΓSpecIso (.of Q)).inv hxy
  have hN := RelativeCurvePencil.sectionPairGraphCoefficient_norm_marked_value
    q (f ≫ π) jB p (retained_source_structure q π f jB jA p hret hA)
    z s hs H e d hd L aS bS hpair f (z ≫ jA)
    (retainedSectionPair_marked_map f jB jA p hret z s hs)
    n φ k σ hn HN u t Hf a hz hj w hw bE hbE
  have hT := sectionPairGraph_norm_targetCoefficient_marked_eq
    q π f jB jA p hret hA z s hs H e d hd L aS bS hpair
    n φ k σ hn HN u t Hf a hz hj w hw bE hbE
    dA hdA LA aA bA hpairA vA wA hgraph l hl
  change φ (Algebra.norm R _) = (Scheme.ΓSpecIso (.of Q)).hom c at hN
  apply hrQ
  change (Scheme.ΓSpecIso (.of Q)).hom c * φ (μ : R) =
    (Scheme.ΓSpecIso (.of Q)).hom c * 1
  rw [← hN, hT, mul_one, mul_comm, ← map_mul, ← hμ, hT]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S C Y W K : Scheme.{u}} (π : C ⟶ S) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (L : LineBundle (pullback (j ≫ π) π))
  (a : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ L (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))).val)
  (b : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ L.val)
  (w : W ⟶ pullback (j ≫ π) π)
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _ L b) w)]
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _
    (tensorLineBundle _ L (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))) a) w)]
  [IsIntegral K] (F : pullback (j ≫ π) π ⟶ K) [IsFinite F]
  (γ : pullback F (K.fromSpecStalk (genericPoint K)) ⟶ W)
  (hγ : γ ≫ w = pullback.fst F (K.fromSpecStalk (genericPoint K)))

include hγ in
/-- The native generic ratio is the inverse of the same graph coefficient.
The ratio is an actual unit of the whole finite generic algebra; no component
is assumed to be a field and nonzero is never substituted for invertibility. -/
theorem sectionPairGraphCoefficient_mul_genericRatio :
    let M := tensorLineBundle _ L (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))
    let c := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) L
      (Hom.idealInclusion (Hom.compactificationGraph π j)) b
    let φ := sectionDualFunctional _ M a
    let ψ := sectionDualFunctional _ M c
    ∀ [Mono φ] [Mono ψ],
      (Scheme.genericFiberLineRatioUnit F (dualLineBundle _ M) φ ψ :
        Γ(pullback F (K.fromSpecStalk (genericPoint K)), ⊤)) *
        γ.appTop (Modules.Hom.app (sectionPairGraphCoefficient π j L a b w) ⊤
          (1 : Γ(W, ⊤))) = 1 := by
  dsimp only
  intro hφ hψ
  let := hφ
  let := hψ
  let M := tensorLineBundle _ L (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))
  let φ := sectionDualFunctional _ M a
  let ψ := sectionDualFunctional _ M
    (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) L
      (Hom.idealInclusion (Hom.compactificationGraph π j)) b)
  have : IsIso (pullbackUnitMap w φ) := by
    change IsIso (Hom.pullbackToUnit (sectionDualFunctional _
      (tensorLineBundle _ L (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))) a) w)
    infer_instance
  let m := Modules.Hom.app (inv (pullbackUnitMap w φ)) ⊤ (1 : Γ(W, ⊤))
  have h := Scheme.genericFiberLineRatioUnit_mul_factorization_section
    F w γ hγ (dualLineBundle _ M) φ ψ m
  have ha : Modules.Hom.app (pullbackUnitMap w φ) ⊤ m = (1 : Γ(W, ⊤)) := by
    change Modules.Hom.app (inv (pullbackUnitMap w φ) ≫ pullbackUnitMap w φ)
      ⊤ (1 : Γ(W, ⊤)) = _
    rw [IsIso.inv_hom_id]
    rfl
  have hc : Modules.Hom.app (pullbackUnitMap w ψ) ⊤ m =
      Modules.Hom.app (sectionPairGraphCoefficient π j L a b w) ⊤ (1 : Γ(W, ⊤)) := by
    change Modules.Hom.app (inv (pullbackUnitMap w φ) ≫ pullbackUnitMap w ψ)
      ⊤ (1 : Γ(W, ⊤)) = _
    have he : inv (pullbackUnitMap w φ) ≫ pullbackUnitMap w ψ =
        sectionPairGraphCoefficient π j L a b w := by
      exact (sectionPairIdealFrame_graphCoefficient w
        (Hom.relativeCompactificationGraphLine π j) L b a
        (Hom.idealInclusion (Hom.compactificationGraph π j))).symm
    exact congrArg (fun θ : (SheafOfModules.unit W.ringCatSheaf : W.Modules) ⟶
      SheafOfModules.unit W.ringCatSheaf =>
        (show Γ(W, ⊤) from Modules.Hom.app θ ⊤ (1 : Γ(W, ⊤)))) he
  calc
    _ = (Scheme.genericFiberLineRatioUnit F (dualLineBundle _ M) φ ψ :
        Γ(pullback F (K.fromSpecStalk (genericPoint K)), ⊤)) *
        γ.appTop (Modules.Hom.app (pullbackUnitMap w ψ) ⊤ m) :=
      congrArg (fun x : Γ(W, ⊤) =>
        (Scheme.genericFiberLineRatioUnit F (dualLineBundle _ M) φ ψ :
          Γ(pullback F (K.fromSpecStalk (genericPoint K)), ⊤)) * γ.appTop x) hc.symm
    _ = γ.appTop (Modules.Hom.app (pullbackUnitMap w φ) ⊤ m) := h
    _ = γ.appTop (1 : Γ(W, ⊤)) := congrArg (fun x : Γ(W, ⊤) => γ.appTop x) ha
    _ = 1 := map_one γ.appTop.hom

end AlgebraicGeometry.Scheme.RelativeCurvePencil
