/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.Norm.GraphCancelledNormDifference
public import Motivic.Transfers.Presheaf.Actions.Pencils.CorrectionBoundary
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.PrincipalOrderOpenExtension
public import Motivic.AlgebraicGeometry.Correspondences.Support.OpenTargetFaithfulness


/-! # Return the original graph-cancelled norm comparison to the marked complement

Only the original numerator and pole are required to be units on the full
marked boundaries. Graph-pole cancellation is performed on enlarged curves,
then actual open extensions and faithfulness of finite correspondences return
the equality to the original marked complement.
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

/-- Compare the same original marked-complement correspondences by cancelling
actual graph terms on the enlarged curves and returning through the original
open maps. No graph-twisted pole unit on the marked boundary is assumed. -/
theorem boundarySection_norm_difference_marked
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
    (φ : X ⟶ Y) (hφ : δT ≫ g = φ.left)
    (Z : SmoothSite (Spec (.of k))) (u : Z ⟶ Y) [IsOpenImmersion u.left]
    (U₀ B₀ : Fin 2 → Scheme.{u}) (i₀ : ∀ t, B₀ t ⟶ C t)
    (l₀ : ∀ t, U₀ t ⟶ C t) [∀ t, IsOpenImmersion (l₀ t)]
    [∀ t, (U₀ t).IsQuasiAffine]
    [∀ t, SmoothOfRelativeDimension 1 (l₀ t ≫ (f t ≫ q))]
    (v₀ : ∀ t, U₀ t ⟶ U t) (hv₀ : ∀ t, v₀ t ≫ l t = l₀ t)
    (hc₀ : ∀ t (x : C t), x ∈ Set.range (l₀ t) ∨ x ∈ Set.range (i₀ t))
    [∀ t, IsIso (pullbackSectionMap (i₀ t) (aS t))]
    [∀ t, IsIso (pullbackSectionMap (i₀ t) (bS t))]
    (g₀ : ∀ t, U₀ t ⟶ Z.left)
    (hb₀ : ∀ t, (l₀ t ≫ (f t ≫ q)) ≫ X.hom = g₀ t ≫ Z.hom)
    (hgu₀ : ∀ t, g₀ t ≫ u.left = v₀ t ≫ (w t ≫ g))
    {V₀ : Scheme.{u}} (j₀ : V₀ ⟶ T) [IsOpenImmersion j₀]
    [V₀.IsQuasiAffine] [SmoothOfRelativeDimension 1 (j₀ ≫ q)]
    (v : V₀ ⟶ V) (hv : v ≫ j = j₀)
    (hW₀ : (Set.range j₀)ᶜ ⊆ (W : Set T))
    (gT₀ : V₀ ⟶ Z.left) (hbT₀ : j₀ ≫ q ≫ X.hom = gT₀ ≫ Z.hom)
    (hguT₀ : gT₀ ≫ u.left = v ≫ g) :
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
    let d := fun t => boundarySection X Z (i₀ t) (f t ≫ q) (l₀ t) (A t)
        (hc₀ t) (g₀ t) (hb₀ t) (aS t) -
      boundarySection X Z (i₀ t) (f t ≫ q) (l₀ t) (M t)
        (hc₀ t) (g₀ t) (hb₀ t) (bS t)
    d 0 - d 1 = PrincipalOrderCorrespondence.correspondence q j₀ W hW₀ r hr gT₀ hbT₀ := by
  let I := fun t => (⟨Scheme.Hom.idealModule (γ t), hI t⟩ : LineBundle (C t))
  let A := fun t => tensorLineBundle (C t) (M t) (dualLineBundle (C t) (I t))
  dsimp only
  intro hg
  let hbase := fun t => show (l t ≫ (f t ≫ q)) ≫ X.hom = (w t ≫ g) ≫ Y.hom from
    by simpa only [← Category.assoc, (H t).w] using congrArg (w t ≫ ·) hb
  have hn := boundarySection_norm_difference_cancel_graph X Y q j C U B f i l w H
    γ hI δ hδ γT δT hδT htriangle hq M aS bS hc hnormal hfree W hW r hr
    g hb φ hφ hg
  let : ∀ t, IsIso ((Scheme.Modules.pullback (i t)).map
      (sectionDualFunctional (C t) (A t) (aS t))) :=
    fun t => sectionDualFunctional_pullback_map_isIso (i t) (A t) (aS t)
  let : ∀ t, IsIso ((Scheme.Modules.pullback (i₀ t)).map
      (sectionDualFunctional (C t) (A t) (aS t))) :=
    fun t => sectionDualFunctional_pullback_map_isIso (i₀ t) (A t) (aS t)
  let : ∀ t, IsIso ((Scheme.Modules.pullback (i t)).map
      (sectionDualFunctional (C t) (M t) (bS t))) :=
    fun t => sectionDualFunctional_pullback_map_isIso (i t) (M t) (bS t)
  let : ∀ t, IsIso ((Scheme.Modules.pullback (i₀ t)).map
      (sectionDualFunctional (C t) (M t) (bS t))) :=
    fun t => sectionDualFunctional_pullback_map_isIso (i₀ t) (M t) (bS t)
  have ha (t : Fin 2) := boundaryFunctional_comp_graph_of_open_extension X Z Y
    (i₀ t) (i t) (f t ≫ q) (l₀ t) (l t) (v₀ t) (hv₀ t)
    (dualLineBundle (C t) (A t)) (sectionDualFunctional (C t) (A t) (aS t))
    (hc₀ t) (hc t) (g₀ t) (hb₀ t) (w t ≫ g) (hbase t) u (hgu₀ t)
  have hb' (t : Fin 2) := boundaryFunctional_comp_graph_of_open_extension X Z Y
    (i₀ t) (i t) (f t ≫ q) (l₀ t) (l t) (v₀ t) (hv₀ t)
    (dualLineBundle (C t) (M t)) (sectionDualFunctional (C t) (M t) (bS t))
    (hc₀ t) (hc t) (g₀ t) (hb₀ t) (w t ≫ g) (hbase t) u (hgu₀ t)
  apply comp_open_graph_injective u
  dsimp only
  erw [Preadditive.sub_comp, Preadditive.sub_comp, Preadditive.sub_comp]
  dsimp only [boundarySection]
  erw [ha 0, hb' 0, ha 1, hb' 1,
    PrincipalOrderCorrespondence.correspondence_comp_graph_of_open_extension
      X Z Y q j₀ j v hv W hW₀ hW r hr gT₀ hbT₀ g
        (by simpa only [Category.assoc] using hb) u hguT₀]
  exact hn

end Motivic.Cor
