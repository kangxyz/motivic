/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairGraphMarkedNorm
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.RetainedMarkedCoordinateComparison

/-! # The original source graph norm has the native target marked value

The original retained map determines both marked factors. The entire residual
still factors through the chosen thickened boundary, and only the total chart
algebra is required to be free.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Norm.RetainedSectionPairGraph`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Norm.SectionPairBoundaryEquality`.
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
  (jA : X ⟶ P) (p : Y ⟶ X) [Flat p]
  (hret : jB ≫ f = p ≫ jA) (hA : jA ≫ π = q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget q z))
  (d : D ⟶ C) (hd : Disjoint (Set.range jB) (Set.range d))

omit [IsFinite f] [IsOpenImmersion jB] [Flat p] in
include hret hs in
/-- The literal marked section equation for the original retained map. -/
theorem retainedSectionPair_marked_map : (s ≫ jB) ≫ f = z ≫ jA := by
  simp only [Category.assoc, hret, ← Category.assoc s, hs]

omit [IsSeparated q] [SmoothOfRelativeDimension 1 q] [IsSeparated π] in
include hA in
/-- The native target is viewed with its identity retained parameter. -/
theorem retainedSectionPair_target_structure : jA ≫ π = (𝟙 X) ≫ q := by
  simpa only [Category.id_comp] using hA

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

omit [IsSeparated π] [IsFinite f] [IsOpenImmersion jB]
  [SmoothOfRelativeDimension 1 (jB ≫ f ≫ π)] [IsOpenImmersion k] in
include hj hw in
/-- The marked point on the actual source chart retains its original projection. -/
theorem retainedSectionPair_chart_point :
    ((σ ≫ k) ≫ w) ≫ pullback.snd (jB ≫ f ≫ π) (f ≫ π) = a ≫ s ≫ jB := by
  calc
    _ = (σ ≫ k) ≫ u := by
      simpa only [Category.assoc] using congrArg (fun m => (σ ≫ k) ≫ m) hw
    _ = _ := hj.symm

include hpair hn HN Hf hz hbE hj hw in
/-- The determinant norm of the original source graph scalar has the actual
native target marked coordinate, with exactly the same supplied ideal frame. -/
theorem retainedSectionPairGraph_norm_target_value :
    let c : Γ(T, ⊤) := Modules.Hom.app
      (RelativeCurvePencil.sectionPairGraphCoefficient (f ≫ π) jB L aS bS w) ⊤
      (1 : Γ(T, ⊤))
    let γ := (σ ≫ k) ≫ w
    let hp := retainedSectionPair_chart_point π f jB s k σ u a hj w hw
    let rT := retainedNativeTargetMarkedFactor π f jB jA p hret z s hs γ a hp
    let mT := Modules.Hom.app (unitEndomorphismPullback
      (rT ≫ (relativeBoundaryProductIso q π jA (𝟙 X)
        (retainedSectionPair_target_structure q π jA hA)
        z z (Category.comp_id z)).hom ≫ boundaryProductMap q (𝟙 X) z)
      (e.hom ≫ idealInclusion (boundaryGraphTarget q z))) ⊤ (1 : Γ(Spec (.of Q), ⊤))
    let : Algebra R Γ(T, ⊤) := (FiniteSchemeNormBaseChange.scalarMap n).toAlgebra
    ∀ [Module.Free R Γ(T, ⊤)],
      φ (Algebra.norm R c) = (Scheme.ΓSpecIso (.of Q)).hom mT := by
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
    have hN := RelativeCurvePencil.sectionPairGraphCoefficient_norm_marked_value q (f ≫ π) jB p
      (retained_source_structure q π f jB jA p hret hA) z s hs H e d hd L aS bS hpair
      f (z ≫ jA) (retainedSectionPair_marked_map f jB jA p hret z s hs)
      n φ k σ hn HN u t Hf a hz hj w hw bE hbE
    let γ := (σ ≫ k) ≫ w
    have hp := retainedSectionPair_chart_point π f jB s k σ u a hj w hw
    have hfactor : Scheme.graphChartMarkedFactor (f ≫ π) jB s k σ u a hj
        w hw = retainedSourceMarkedFactor π f jB s γ a hp := by
      apply (graphBoundaryRestriction_isPullback (f ≫ π) jB s).hom_ext
      · dsimp only [retainedSourceMarkedFactor]
        rw [IsPullback.lift_fst]
        exact Scheme.graphChartMarkedFactor_ambient (f ≫ π) jB s k σ u a hj w hw
      · simp [Scheme.graphChartMarkedFactor, retainedSourceMarkedFactor]
    have hm := retainedMarkedCoordinate_eq q π f jB jA p hret hA z s hs γ a hp
    have hmap := (congrArg (fun r : Spec (.of Q) ⟶
        pullback (jB ≫ f ≫ π) (s ≫ jB ≫ f ≫ π) => r ≫
        (relativeBoundaryProductIso q (f ≫ π) jB p
          (retained_source_structure q π f jB jA p hret hA) z s hs).hom ≫
            boundaryProductMap q p z) hfactor).trans hm
    have heval := congrArg eval hmap
    with_reducible exact hN.trans heval

end AlgebraicGeometry.Scheme.Hom
