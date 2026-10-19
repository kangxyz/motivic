/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Norm.RetainedSectionPairGraph
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairNativeTargetScalar

/-! # The actual source norm and target coefficient agree on the marked boundary

Both original section pairs use the same marked frame. Their actual retained
chart maps identify the two marked coordinates. Only the original total chart
algebra is assumed free, and the marked graph coefficients may vanish.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Norm.SectionPairBoundaryEquality`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
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

include hpair hpairA hn HN Hf hz hbE hj hw hgraph hl in
/-- The determinant source coefficient and the actual target coefficient have
identical full marked restrictions. All scalar values follow from the original
section choices and actual chart maps; neither graph scalar is inverted. -/
theorem sectionPairGraph_norm_targetCoefficient_marked_eq :
    let cB : Γ(T, ⊤) := Modules.Hom.app
      (RelativeCurvePencil.sectionPairGraphCoefficient (f ≫ π) jB L aS bS w) ⊤
      (1 : Γ(T, ⊤))
    let cA : R := (Scheme.ΓSpecIso (.of R)).hom
      ((l ≫ pullback.snd (retainedParameterProductMap π f jB jA p hret) vA).appTop
        (Modules.Hom.app (RelativeCurvePencil.sectionPairGraphCoefficient π jA LA aA bA vA) ⊤
          (1 : Γ(WA, ⊤))))
    let : Algebra R Γ(T, ⊤) := (FiniteSchemeNormBaseChange.scalarMap n).toAlgebra
    ∀ [Module.Free R Γ(T, ⊤)], φ (Algebra.norm R cB) = φ cA := by
  dsimp only
  intro hfree
  let : Algebra R Γ(T, ⊤) := (FiniteSchemeNormBaseChange.scalarMap n).toAlgebra
  let := hfree
  have hp : ((σ ≫ k) ≫ w) ≫ pullback.snd (jB ≫ f ≫ π) (f ≫ π) = a ≫ s ≫ jB := by
    simpa only [Category.assoc, hw] using hj.symm
  have hN := retainedSectionPairGraph_norm_target_value q π f jB jA p hret hA
    z s hs H e d hd L aS bS hpair n φ k σ hn HN u t Hf a hz hj w hw bE hbE
  have hT := RelativeCurvePencil.sectionPairGraphCoefficient_actual_target_chart_marked_value
    q π f jB jA p hret hA z s hs e dA hdA LA aA bA hpairA vA
    w n wA hgraph l hl (σ ≫ k) a hp
  have hTS := congrArg (fun x : Γ(Spec (.of Q), ⊤) => (Scheme.ΓSpecIso (.of Q)).hom x) hT
  refine hN.trans (hTS.symm.trans ?_)
  let c : Γ(WA, ⊤) := Modules.Hom.app
    (RelativeCurvePencil.sectionPairGraphCoefficient π jA LA aA bA vA) ⊤ (1 : Γ(WA, ⊤))
  have hm : (σ ≫ k) ≫ n ≫ l ≫
      pullback.snd (retainedParameterProductMap π f jB jA p hret) vA =
    Spec.map (CommRingCat.ofHom φ) ≫ l ≫
      pullback.snd (retainedParameterProductMap π f jB jA p hret) vA := by
    rw [← Category.assoc (σ ≫ k) n, hn]
  rw [hm]
  have hnat := congrArg
    (fun m : Γ(Spec (.of R), ⊤) ⟶ CommRingCat.of Q =>
      m ((l ≫ pullback.snd (retainedParameterProductMap π f jB jA p hret) vA).appTop c))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  simpa only [Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.hom_ofHom, c] using hnat

end AlgebraicGeometry.Scheme.Hom
