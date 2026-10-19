/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.BoundaryFunctional.NormComparison
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.Norm.GraphTwistedPoleCorrespondence
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.TwistedIdealRegularity


/-! # Cancel original graph terms before the marked-complement restriction

The retained opens in this theorem are the enlarged curves. The graph-twisted
poles need be units only on their omitted infinity boundaries, not on marked
incidence. Their original graph terms cancel by the actual compactification
triangles before any subsequent passage to the marked complement.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open AlgebraicGeometry.FiniteSchemeNormBaseChange
universe u
namespace Motivic.Cor

/-- The genuine norm quotient compares the original numerator-minus-pole
correspondences after cancelling their common original graph. The hypotheses on
`i` concern infinity only; no graph-pole unit on marked incidence is asserted. -/
theorem boundarySection_norm_difference_cancel_graph
    {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
    {T V : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
    (q : T ⟶ X.left) [IsProper q] (j : V ⟶ T) [IsOpenImmersion j]
    [V.IsQuasiAffine] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (C U B : Fin 2 → Scheme.{u}) (f : ∀ t, C t ⟶ T) [∀ t, IsFinite (f t)]
    (i : ∀ t, B t ⟶ C t) (l : ∀ t, U t ⟶ C t) [∀ t, IsOpenImmersion (l t)]
    [∀ t, (U t).IsQuasiAffine]
    [∀ t, SmoothOfRelativeDimension 1 (l t ≫ (f t ≫ q))]
    (w : ∀ t, U t ⟶ V) (H : ∀ t, IsPullback (l t) (w t) (f t) j)
    (γ : ∀ t, X.left ⟶ C t) [∀ t, IsClosedImmersion (γ t)]
    (hI : ∀ t, IsLocallyRankOne (C t) (Scheme.Hom.idealModule (γ t)))
    (δ : ∀ t, X.left ⟶ U t) (hδ : ∀ t, δ t ≫ l t = γ t)
    (γT : X.left ⟶ T) (δT : X.left ⟶ V) (hδT : δT ≫ j = γT)
    (htriangle : ∀ t, γ t ≫ f t = γT) (hq : γT ≫ q = 𝟙 X.left)
    (M : ∀ t, LineBundle (C t))
    (aS : ∀ t, SheafOfModules.unit (C t).ringCatSheaf ⟶
      (tensorLineBundle (C t) (M t)
        (dualLineBundle (C t) ⟨Scheme.Hom.idealModule (γ t), hI t⟩)).val)
    (bS : ∀ t, SheafOfModules.unit (C t).ringCatSheaf ⟶ (M t).val)
    [∀ t, IsIso (pullbackSectionMap (i t) (aS t))]
    [∀ t, IsIso (pullbackSectionMap (i t) (bS t))]
    [∀ t, IsIso ((Scheme.Modules.pullback (i t)).map (Scheme.Hom.idealInclusion (γ t)))]
    [∀ t, IsIso (pullbackSectionMap (i t)
      (twistedIdealSection (C t) ⟨Scheme.Hom.idealModule (γ t), hI t⟩ (M t)
        (Scheme.Hom.idealInclusion (γ t)) (bS t)))]
    [∀ t, Mono (sectionDualFunctional (C t)
      (tensorLineBundle (C t) (M t)
        (dualLineBundle (C t) ⟨Scheme.Hom.idealModule (γ t), hI t⟩)) (aS t))]
    [∀ t, Mono (sectionDualFunctional (C t) (M t) (bS t))]
    (hc : ∀ t (x : C t), x ∈ Set.range (l t) ∨ x ∈ Set.range (i t))
    (hnormal : ∀ (O : T.Opens), IsAffineOpen O → Nonempty O →
      IsIntegrallyClosed Γ(T, O))
    (hfree : ∀ t (x : T), ∃ (O : T.Opens) (hO : IsAffineOpen O), x ∈ O ∧
      (let : Algebra Γ(T, O) Γ(Limits.pullback (f t) hO.fromSpec, ⊤) :=
        (scalarMap (pullback.snd (f t) hO.fromSpec)).toAlgebra
       Module.Free Γ(T, O) Γ(Limits.pullback (f t) hO.fromSpec, ⊤)))
    (W : T.Opens) [Nonempty W] (hW : (Set.range j)ᶜ ⊆ (W : Set T))
    (r : Γ(T, W)) (hr : IsUnit r)
    (g : V ⟶ Y.left) (hb : (j ≫ q) ≫ X.hom = g ≫ Y.hom)
    (φ : X ⟶ Y) (hφ : δT ≫ g = φ.left) :
    let I := fun t => (⟨Scheme.Hom.idealModule (γ t), hI t⟩ : LineBundle (C t))
    let A := fun t => tensorLineBundle (C t) (M t) (dualLineBundle (C t) (I t))
    let cS := fun t => twistedIdealSection (C t) (I t) (M t)
      (Scheme.Hom.idealInclusion (γ t)) (bS t)
    let a := fun t => sectionDualFunctional (C t) (A t) (aS t)
    let c := fun t => sectionDualFunctional (C t) (A t) (cS t)
    let : ∀ t, Mono (Scheme.Hom.idealInclusion (γ t)) :=
      fun t => Scheme.Hom.idealInclusionMono (γ t)
    let : ∀ t, Mono (c t) := fun t => twistedIdealSection_mono
      (C t) (I t) (M t) (Scheme.Hom.idealInclusion (γ t)) (bS t)
    T.germToFunctionField W r =
        Scheme.genericFiberLineRatioNorm (f 0) (dualLineBundle (C 0) (A 0)) (a 0) (c 0) /
          Scheme.genericFiberLineRatioNorm (f 1) (dualLineBundle (C 1) (A 1)) (a 1) (c 1) →
    let hbase := fun t => show (l t ≫ (f t ≫ q)) ≫ X.hom = (w t ≫ g) ≫ Y.hom from
      by simpa only [← Category.assoc, (H t).w] using congrArg (w t ≫ ·) hb
    let d := fun t => boundarySection X Y (i t) (f t ≫ q) (l t) (A t)
        (hc t) (w t ≫ g) (hbase t) (aS t) -
      boundarySection X Y (i t) (f t ≫ q) (l t) (M t)
        (hc t) (w t ≫ g) (hbase t) (bS t)
    d 0 - d 1 = PrincipalOrderCorrespondence.correspondence q j W hW r hr g
      (by simpa only [Category.assoc] using hb) := by
  let I := fun t => (⟨Scheme.Hom.idealModule (γ t), hI t⟩ : LineBundle (C t))
  let A := fun t => tensorLineBundle (C t) (M t) (dualLineBundle (C t) (I t))
  let cS := fun t => twistedIdealSection (C t) (I t) (M t)
    (Scheme.Hom.idealInclusion (γ t)) (bS t)
  let a := fun t => sectionDualFunctional (C t) (A t) (aS t)
  let c := fun t => sectionDualFunctional (C t) (A t) (cS t)
  let : ∀ t, Mono (Scheme.Hom.idealInclusion (γ t)) :=
    fun t => Scheme.Hom.idealInclusionMono (γ t)
  let : ∀ t, Mono (c t) := fun t => twistedIdealSection_mono
    (C t) (I t) (M t) (Scheme.Hom.idealInclusion (γ t)) (bS t)
  dsimp only
  intro hg
  let : ∀ t, IsIso ((Scheme.Modules.pullback (i t)).map (a t)) :=
    fun t => sectionDualFunctional_pullback_map_isIso (i t) (A t) (aS t)
  let : ∀ t, IsIso ((Scheme.Modules.pullback (i t)).map (c t)) :=
    fun t => sectionDualFunctional_pullback_map_isIso (i t) (A t) (cS t)
  have hn := boundaryFunctional_norm_difference X Y q j C U B f i l w H
    (fun t => dualLineBundle (C t) (A t)) a c hc hnormal hfree W hW r hr hg g hb
  have hδw (t : Fin 2) : δ t ≫ w t = δT := by
    apply (cancel_mono j).mp
    calc
      (δ t ≫ w t) ≫ j = δ t ≫ (l t ≫ f t) := by rw [Category.assoc, (H t).w]
      _ = γ t ≫ f t := by rw [← Category.assoc, hδ]
      _ = δT ≫ j := (htriangle t).trans hδT.symm
  let hbase := fun t => show (l t ≫ (f t ≫ q)) ≫ X.hom = (w t ≫ g) ≫ Y.hom from
    by simpa only [← Category.assoc, (H t).w] using congrArg (w t ≫ ·) hb
  have hgraph (t : Fin 2) := boundarySection_twistedIdeal_eq_graph_add X Y
    (i t) (f t ≫ q) (l t) (γ t) (hI t) (δ t) (hδ t)
    (by rw [← Category.assoc, htriangle, hq]) (M t) (bS t) (hc t)
    (w t ≫ g) φ (by rw [← Category.assoc, hδw, hφ]) (hbase t)
  change (boundarySection X Y (i 0) (f 0 ≫ q) (l 0) (A 0)
      (hc 0) (w 0 ≫ g) (hbase 0) (aS 0) -
      boundarySection X Y (i 0) (f 0 ≫ q) (l 0) (A 0)
        (hc 0) (w 0 ≫ g) (hbase 0) (cS 0)) -
    (boundarySection X Y (i 1) (f 1 ≫ q) (l 1) (A 1)
      (hc 1) (w 1 ≫ g) (hbase 1) (aS 1) -
      boundarySection X Y (i 1) (f 1 ≫ q) (l 1) (A 1)
        (hc 1) (w 1 ≫ g) (hbase 1) (cS 1)) = _ at hn
  rw [hgraph 0, hgraph 1] at hn
  change _ - (((graphFunctor k).map φ : Cor.mk X ⟶ Cor.mk Y) + _) -
    (_ - (((graphFunctor k).map φ : Cor.mk X ⟶ Cor.mk Y) + _)) = _ at hn
  have halg (a b c d g : Cor.mk X ⟶ Cor.mk Y) :
      (a - b) - (c - d) = (a - (g + b)) - (c - (g + d)) := by abel
  exact (halg _ _ _ _ _).trans hn

end Motivic.Cor
