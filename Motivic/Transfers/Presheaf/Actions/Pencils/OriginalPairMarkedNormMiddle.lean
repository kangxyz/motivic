/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.Norm.OriginalPairMarkedNormProduct
public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeCorrectionPairMiddle

/-! # The marked product comparison with the shared middle correspondence

This theorem retains the original marked-product hypotheses and principal
correspondence. Only its left-hand expression is named by the existing ordinary
middle definition, with the conversion performed at generic variables.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open AlgebraicGeometry.FiniteSchemeNormBaseChange
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
universe u
namespace Motivic.Cor

/-- The original marked product comparison lands in the shared middle, with
all original geometric, unit, and norm-germ hypotheses unchanged. -/
theorem originalPair_norm_product_marked_middle
    {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
    (O : Fin 2 → SmoothSite (Spec (.of k))) [∀ t, IsAffine (O t).left]
    (α : ∀ t, X ⟶ O t) [∀ t, Flat (α t).left]
    {T V : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
    (q : T ⟶ X.left) [IsProper q] (jT : V ⟶ T) [IsOpenImmersion jT]
    [V.IsQuasiAffine] [SmoothOfRelativeDimension 1 (jT ≫ q)]
    (C U B C₀ U₀ B₀ : Fin 2 → Scheme.{u})
    (f : ∀ t, C t ⟶ T) [∀ t, IsFinite (f t)]
    (i : ∀ t, B t ⟶ C t) (j : ∀ t, U t ⟶ C t)
    [∀ t, IsOpenImmersion (j t)] [∀ t, (U t).IsQuasiAffine]
    [∀ t, SmoothOfRelativeDimension 1 (j t ≫ (f t ≫ q))]
    (w : ∀ t, U t ⟶ V) (hw : ∀ t, j t ≫ f t = w t ≫ jT)
    (q₀ : ∀ t, C₀ t ⟶ (O t).left) [∀ t, IsProper (q₀ t)]
    (i₀ : ∀ t, B₀ t ⟶ C₀ t) (j₀ : ∀ t, U₀ t ⟶ C₀ t)
    [∀ t, IsOpenImmersion (j₀ t)] [∀ t, (U₀ t).IsQuasiAffine]
    [∀ t, SmoothOfRelativeDimension 1 (j₀ t ≫ q₀ t)]
    (c : ∀ t, C t ⟶ C₀ t) (v : ∀ t, U t ⟶ U₀ t)
    (hv : ∀ t, v t ≫ j₀ t = j t ≫ c t)
    (Hp : ∀ t, IsPullback (v t) (j t ≫ (f t ≫ q)) (j₀ t ≫ q₀ t) (α t).left)
    (γ : (O 0).left ⟶ C₀ 0) [IsClosedImmersion γ]
    (hI : IsLocallyRankOne (C₀ 0) (Scheme.Hom.idealModule γ))
    (δ : (O 0).left ⟶ U₀ 0) (hδ : δ ≫ j₀ 0 = γ)
    (hq : γ ≫ q₀ 0 = 𝟙 (O 0).left)
    (M : LineBundle (C₀ 0))
    (aS : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶
      (tensorLineBundle (C₀ 0) M
        (dualLineBundle (C₀ 0) ⟨Scheme.Hom.idealModule γ, hI⟩)).val)
    (bS : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ M.val)
    [IsIso (pullbackSectionMap (i₀ 0) aS)]
    [IsIso (pullbackSectionMap (i₀ 0) bS)]
    [IsIso ((Scheme.Modules.pullback (i₀ 0)).map (Scheme.Hom.idealInclusion γ))]
    [IsIso (pullbackSectionMap (i₀ 0)
      (twistedIdealSection (C₀ 0) ⟨Scheme.Hom.idealModule γ, hI⟩ M
        (Scheme.Hom.idealInclusion γ) bS))]
    (N : LineBundle (C₀ 1))
    (nS dS : N.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf)
    [IsIso ((Scheme.Modules.pullback (i₀ 1)).map nS)]
    [IsIso ((Scheme.Modules.pullback (i₀ 1)).map dS)]
    (hc : ∀ t (x : C t), x ∈ Set.range (j t) ∨ x ∈ Set.range (i t))
    (hc₀ : ∀ t (x : C₀ t), x ∈ Set.range (j₀ t) ∨ x ∈ Set.range (i₀ t))
    (g : V ⟶ Y.left) (hb : (jT ≫ q) ≫ X.hom = g ≫ Y.hom)
    (g₀ : ∀ t, U₀ t ⟶ Y.left)
    (hb₀ : ∀ t, (j₀ t ≫ q₀ t) ≫ (O t).hom = g₀ t ≫ Y.hom)
    (hgv : ∀ t, v t ≫ g₀ t = w t ≫ g)
    (φ : O 0 ⟶ Y) (hφ : δ ≫ g₀ 0 = φ.left)
    (hnormal : ∀ (W : T.Opens), IsAffineOpen W → Nonempty W → IsIntegrallyClosed Γ(T, W))
    (hfree : ∀ t (x : T), ∃ (W : T.Opens) (hW : IsAffineOpen W), x ∈ W ∧
      (let : Algebra Γ(T, W) Γ(Limits.pullback (f t) hW.fromSpec, ⊤) :=
        (scalarMap (pullback.snd (f t) hW.fromSpec)).toAlgebra
       Module.Free Γ(T, W) Γ(Limits.pullback (f t) hW.fromSpec, ⊤)))
    (W : T.Opens) [Nonempty W] (hW : (Set.range jT)ᶜ ⊆ (W : Set T))
    (R : Γ(T, W)) (hR : IsUnit R)
    (Z : SmoothSite (Spec (.of k))) (u : Z ⟶ Y) [IsOpenImmersion u.left]
    (U₁ B₁ : Fin 2 → Scheme.{u}) (i₁ : ∀ t, B₁ t ⟶ C₀ t)
    (j₁ : ∀ t, U₁ t ⟶ C₀ t) [∀ t, IsOpenImmersion (j₁ t)]
    [∀ t, (U₁ t).IsQuasiAffine]
    [∀ t, SmoothOfRelativeDimension 1 (j₁ t ≫ q₀ t)]
    (v₁ : ∀ t, U₁ t ⟶ U₀ t) (hv₁ : ∀ t, v₁ t ≫ j₀ t = j₁ t)
    (hc₁ : ∀ t (x : C₀ t), x ∈ Set.range (j₁ t) ∨ x ∈ Set.range (i₁ t))
    [IsIso (pullbackSectionMap (i₁ 0) aS)]
    [IsIso (pullbackSectionMap (i₁ 0) bS)]
    [IsIso ((Scheme.Modules.pullback (i₁ 1)).map nS)]
    [IsIso ((Scheme.Modules.pullback (i₁ 1)).map dS)]
    (g₁ : ∀ t, U₁ t ⟶ Z.left)
    (hb₁ : ∀ t, (j₁ t ≫ q₀ t) ≫ (O t).hom = g₁ t ≫ Z.hom)
    (hgu₁ : ∀ t, g₁ t ≫ u.left = v₁ t ≫ g₀ t)
    (r : X ⟶ Z) (hru : r ≫ u = α 0 ≫ φ)
    {V₁ : Scheme.{u}} (jT₁ : V₁ ⟶ T) [IsOpenImmersion jT₁]
    [V₁.IsQuasiAffine] [SmoothOfRelativeDimension 1 (jT₁ ≫ q)]
    (vT : V₁ ⟶ V) (hvT : vT ≫ jT = jT₁)
    (hW₁ : (Set.range jT₁)ᶜ ⊆ (W : Set T))
    (gT₁ : V₁ ⟶ Z.left) (hbT₁ : jT₁ ≫ q ≫ X.hom = gT₁ ≫ Z.hom)
    (hguT₁ : gT₁ ≫ u.left = vT ≫ g) :
    let I : LineBundle (C₀ 0) := ⟨Scheme.Hom.idealModule γ, hI⟩
    let A := tensorLineBundle (C₀ 0) M (dualLineBundle (C₀ 0) I)
    let af := sectionDualFunctional (C₀ 0) A aS
    let bf := sectionDualFunctional (C₀ 0) M bS
    let cf := sectionDualFunctional (C₀ 0) A
      (twistedIdealSection (C₀ 0) I M (Scheme.Hom.idealInclusion γ) bS)
    let aT := Hom.pullbackToUnit af (c 0)
    let cT := Hom.pullbackToUnit cf (c 0)
    let nT := Hom.pullbackToUnit nS (c 1)
    let dT := Hom.pullbackToUnit dS (c 1)
    ∀ [Mono aT] [Mono cT] [Mono nT] [Mono dT]
      [IsIso ((Scheme.Modules.pullback (i 0)).map aT)]
      [IsIso ((Scheme.Modules.pullback (i 0)).map cT)]
      [IsIso ((Scheme.Modules.pullback (i 1)).map nT)]
      [IsIso ((Scheme.Modules.pullback (i 1)).map dT)]
      [IsIso ((Scheme.Modules.pullback (i 0)).map (Hom.pullbackToUnit bf (c 0)))],
    T.germToFunctionField W R =
      Scheme.genericFiberLineRatioNorm (f 0)
        (pullbackLineBundle (c 0) (dualLineBundle (C₀ 0) A)) aT cT *
      Scheme.genericFiberLineRatioNorm (f 1) (pullbackLineBundle (c 1) N) nT dT →
    @originalPairMarkedMiddle k inferInstance X Z O (fun _ => inferInstance) α
      C₀ U₁ B₁ q₀ (fun _ => inferInstance) i₁ j₁
      (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
      γ hI M aS bS N nS dS hc₁
      inferInstance inferInstance inferInstance inferInstance g₁ hb₁ r =
      PrincipalOrderCorrespondence.correspondence q jT₁ W hW₁ R hR gT₁ hbT₁ := by
  dsimp only
  intro haMono hcMono hnMono hdMono haUnit hcUnit hnUnit hdUnit hbUnit hg
  unfold originalPairMarkedMiddle
  exact originalPair_norm_product_marked X Y O α q jT C U B C₀ U₀ B₀ f i j w hw
    q₀ i₀ j₀ c v hv Hp γ hI δ hδ hq M aS bS N nS dS hc hc₀
    g hb g₀ hb₀ hgv φ hφ hnormal hfree W hW R hR
    Z u U₁ B₁ i₁ j₁ v₁ hv₁ hc₁ g₁ hb₁ hgu₁ r hru
    jT₁ vT hvT hW₁ gT₁ hbT₁ hguT₁ hg

end Motivic.Cor
