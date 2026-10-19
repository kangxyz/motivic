/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Norm.PrescribedGraphMarked
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.RetainedMarkedCoordinateComparison

/-! # The original source graph norm has the native target marked value

The original retained map determines both marked factors. The entire residual
still factors through the chosen thickened boundary, and only the total chart
algebra is required to be free.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Norm.RetainedPrescribedGraph`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

private theorem graph_chart_marked_factor_eq_lift
    {S C Y Z T V Q : Scheme.{u}} (π : C ⟶ S) (j : Y ⟶ C) (s : Z ⟶ Y)
    (k : V ⟶ T) (σ : Q ⟶ V) (u : T ⟶ C) (a : Q ⟶ Z)
    (hj : a ≫ (s ≫ j) = (σ ≫ k) ≫ u)
    (v : T ⟶ pullback (j ≫ π) π) (hv : v ≫ pullback.snd (j ≫ π) π = u)
    (hp : ((σ ≫ k) ≫ v) ≫ pullback.snd (j ≫ π) π = a ≫ (s ≫ j)) :
    Scheme.graphChartMarkedFactor π j s k σ u a hj v hv =
      (graphBoundaryRestriction_isPullback π j s).lift ((σ ≫ k) ≫ v) a hp := by
  apply (graphBoundaryRestriction_isPullback π j s).hom_ext
  · rw [IsPullback.lift_fst]
    exact Scheme.graphChartMarkedFactor_ambient π j s k σ u a hj v hv
  · simp [Scheme.graphChartMarkedFactor]

variable {S X Y Z C P D : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (π : P ⟶ S) [IsSeparated π]
  (f : C ⟶ P) [IsFinite f] (jB : Y ⟶ C) [IsOpenImmersion jB]
  [SmoothOfRelativeDimension 1 (jB ≫ f ≫ π)]
  (jA : X ⟶ P) (p : Y ⟶ X) [Flat p]
  (hret : jB ≫ f = p ≫ jA) (hA : jA ≫ π = q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget q z))
  (d : D ⟶ C) (hd : Disjoint (Set.range jB) (Set.range d))

omit [IsFinite f] [IsOpenImmersion jB] [Flat p] in
include hret hs in
/-- The original marked section commutes with the original compactification map. -/
theorem retainedMarkedPoint : (s ≫ jB) ≫ f = z ≫ jA := by
  simp only [Category.assoc, hret, ← Category.assoc s, hs]

variable (A : (pullback (jB ≫ f ≫ π) (f ≫ π)).affineOpens)
  (b : (pullback (pullback.snd (jB ≫ f ≫ π) (f ≫ π)) d ⨿
    pullback (jB ≫ f ≫ π) (s ≫ jB ≫ f ≫ π)) ⟶ A.val.toScheme)
  (hc : b ≫ A.val.ι =
    coprod.desc (infinityProductMap (f ≫ π) jB d) (graphBoundaryRestriction (f ≫ π) jB s))
  (E : PrescribedAffineFrameExtension A b (relativeCompactificationGraphLine (f ≫ π) jB)
    ((Modules.pullbackComp b A.val.ι).app
        (relativeCompactificationGraphLine (f ≫ π) jB).val ≪≫
      (Modules.pullbackCongr hc).app (relativeCompactificationGraphLine (f ≫ π) jB).val ≪≫
      relativeFullBoundaryIdealFrame q (f ≫ π) jB p
        (retained_source_structure q π f jB jA p hret hA) z s hs H e d hd))

variable {R Q : Type u} [CommRing R] [CommRing Q] {T V : Scheme.{u}}
  (n : T ⟶ Spec (.of R)) [IsFinite n] (φ : R →+* Q)
  (k : V ⟶ T) [IsOpenImmersion k] (σ : Spec (.of Q) ⟶ V)
  (hn : (σ ≫ k) ≫ n = Spec.map (CommRingCat.ofHom φ))
  (HN : IsPullback σ (𝟙 _) (k ≫ n) (Spec.map (CommRingCat.ofHom φ)))
  (u : T ⟶ C) (t : Spec (.of R) ⟶ P) (Hf : IsPullback u n f t)
  (a : Spec (.of Q) ⟶ Z)
  (hz : Spec.map (CommRingCat.ofHom φ) ≫ t = a ≫ (z ≫ jA))
  (hj : a ≫ (s ≫ jB) = (σ ≫ k) ≫ u)
  (w : T ⟶ E.neighborhood)
  (hw : (w ≫ E.ambientInclusion) ≫ pullback.snd (jB ≫ f ≫ π) (f ≫ π) = u)
  (bE : (Scheme.residualMarkedFiberOpen f jB (z ≫ jA) s
    (retainedMarkedPoint f jB jA p hret z s hs)).toScheme ⟶ D)
  (hbE : bE ≫ d = Scheme.residualMarkedFiberMap f jB (z ≫ jA) s
    (retainedMarkedPoint f jB jA p hret z s hs))

include hn HN Hf hz hbE hj hw in
/-- The determinant norm of the original source graph scalar has the actual
native target marked coordinate, with exactly the same supplied ideal frame. -/
theorem retainedPrescribedGraph_norm_target_value :
    let c := Modules.Hom.app
      (E.frame.inv ≫ pullbackUnitMap E.inclusion
        (pullbackUnitMap A.val.ι (idealInclusion (compactificationGraph (f ≫ π) jB)))) ⊤
      (1 : Γ(E.neighborhood, ⊤))
    let γ := (σ ≫ k) ≫ (w ≫ E.ambientInclusion)
    let hp : γ ≫ pullback.snd (jB ≫ f ≫ π) (f ≫ π) = a ≫ s ≫ jB := by
      calc
        γ ≫ pullback.snd (jB ≫ f ≫ π) (f ≫ π) = (σ ≫ k) ≫ u := by
          simpa only [γ, Category.assoc] using congrArg (fun m => (σ ≫ k) ≫ m) hw
        _ = a ≫ s ≫ jB := hj.symm
    let rT := retainedNativeTargetMarkedFactor π f jB jA p hret z s hs γ a hp
    let mT := Modules.Hom.app (unitEndomorphismPullback
      (rT ≫ (relativeBoundaryProductIso q π jA (𝟙 X) (by simpa using hA)
        z z (by simp)).hom ≫ boundaryProductMap q (𝟙 X) z)
      (e.hom ≫ idealInclusion (boundaryGraphTarget q z))) ⊤ (1 : Γ(Spec (.of Q), ⊤))
    let : Algebra R Γ(T, ⊤) := (FiniteSchemeNormBaseChange.scalarMap n).toAlgebra
    ∀ [Module.Free R Γ(T, ⊤)],
      φ (Algebra.norm R (w.appTop c)) = (Scheme.ΓSpecIso (.of Q)).hom mT := by
  let RT : CommRingCat := Γ(T, ⊤)
  let eval : (Spec (.of Q) ⟶ pullback q (z ≫ q)) → Q := fun m =>
    (Scheme.ΓSpecIso (.of Q)).hom (Modules.Hom.app
      (unitEndomorphismPullback m (e.hom ≫ idealInclusion (boundaryGraphTarget q z))) ⊤
      (1 : Γ(Spec (.of Q), ⊤)))
  with_reducible
    dsimp only
    intro hfree
    let : Algebra R RT := (FiniteSchemeNormBaseChange.scalarMap n).toAlgebra
    let := hfree
    have hN := prescribedGraphFrame_norm_marked_value q (f ≫ π) jB p
      (retained_source_structure q π f jB jA p hret hA) z s hs H e d hd A b hc E
      f (z ≫ jA) (retainedMarkedPoint f jB jA p hret z s hs)
      n φ k σ hn HN u t Hf a hz hj w hw bE hbE
    let γ := (σ ≫ k) ≫ (w ≫ E.ambientInclusion)
    have hp : γ ≫ pullback.snd (jB ≫ f ≫ π) (f ≫ π) = a ≫ s ≫ jB := by
      calc
        γ ≫ pullback.snd (jB ≫ f ≫ π) (f ≫ π) = (σ ≫ k) ≫ u := by
          simpa only [γ, Category.assoc] using congrArg (fun m => (σ ≫ k) ≫ m) hw
        _ = a ≫ s ≫ jB := hj.symm
    have hfactor : Scheme.graphChartMarkedFactor (f ≫ π) jB s k σ u a hj
        (w ≫ E.ambientInclusion) hw = retainedSourceMarkedFactor π f jB s γ a hp := by
      simpa only [retainedSourceMarkedFactor, γ] using
        graph_chart_marked_factor_eq_lift (f ≫ π) jB s k σ u a hj
          (w ≫ E.ambientInclusion) hw hp
    have hm := retainedMarkedCoordinate_eq q π f jB jA p hret hA z s hs γ a hp
    have hmap := (congrArg (fun r : Spec (.of Q) ⟶
        pullback (jB ≫ f ≫ π) (s ≫ jB ≫ f ≫ π) => r ≫
        (relativeBoundaryProductIso q (f ≫ π) jB p
          (retained_source_structure q π f jB jA p hret hA) z s hs).hom ≫
            boundaryProductMap q p z) hfactor).trans hm
    have heval := congrArg eval hmap
    with_reducible exact hN.trans heval

end AlgebraicGeometry.Scheme.Hom
