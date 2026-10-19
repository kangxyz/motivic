/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.Norm.OriginalPairNormProduct
public import Motivic.Transfers.Presheaf.Actions.Pencils.CorrectionBoundary
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.PrincipalOrderOpenExtension
public import Motivic.AlgebraicGeometry.Correspondences.Support.OpenTargetFaithfulness


/-! # Original product-norm comparison on the marked complement

The target pair is numerator minus its original pole. The correction has the
opposite order, denominator minus numerator. Only the target is graph-twisted.
Both compact parameter changes are literal pullbacks of the original module
functionals. All omitted-boundary units concern the enlarged, infinity-only
curves. No marked graph-pole unit or correspondence comparison is an input.
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

private theorem parameter_pair_extension {D : Type*} [Category D] [Preadditive D]
    {X O Y Z : D} (u : X ⟶ O) {f : Y ⟶ Z} {a b : O ⟶ Y} {a' b' : O ⟶ Z}
    (ha : a ≫ f = a') (hb : b ≫ f = b') :
    (u ≫ (a - b)) ≫ f = u ≫ (a' - b') := by
  rw [Category.assoc, Preadditive.sub_comp, ha, hb]

private theorem product_eq_of_postcomp_eq {D : Type*} [Category D] [Preadditive D]
    {X Y Z : D} {f : Y ⟶ Z} {a₀ a₁ g p : X ⟶ Y} {b₀ b₁ h q : X ⟶ Z}
    (hf : Function.Injective (fun a : X ⟶ Y => a ≫ f))
    (h₀ : a₀ ≫ f = b₀) (h₁ : a₁ ≫ f = b₁)
    (hg : g ≫ f = h) (hp : p ≫ f = q)
    (hbig : b₀ - b₁ - h = q) : a₀ - a₁ - g = p := by
  apply hf
  dsimp only
  rw [Preadditive.sub_comp, Preadditive.sub_comp, h₀, h₁, hg, hp, hbig]

/-- The genuine product norm gives the original target-minus-correction-minus-
graph correspondence. The correction is `dS - nS`, not its negative. The final
graph factors through the marked open by an equality of site maps. Only original
a/b/n/d units are required on marked boundaries; the same full-boundary unit `R`
defines the principal correspondence before and after extension. -/
theorem originalPair_norm_product_marked
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
    let target : Cor.mk X ⟶ Cor.mk Z := ((graphFunctor k).map (α 0) : Cor.mk X ⟶ Cor.mk (O 0)) ≫
      (boundarySection (O 0) Z (i₁ 0) (q₀ 0) (j₁ 0) A (hc₁ 0) (g₁ 0) (hb₁ 0) aS -
        boundarySection (O 0) Z (i₁ 0) (q₀ 0) (j₁ 0) M (hc₁ 0) (g₁ 0) (hb₁ 0) bS)
    let correction : Cor.mk X ⟶ Cor.mk Z := ((graphFunctor k).map (α 1) : Cor.mk X ⟶ Cor.mk (O 1)) ≫
        (boundaryFunctional (O 1) Z (i₁ 1) (q₀ 1) (j₁ 1) N dS (hc₁ 1) (g₁ 1) (hb₁ 1) -
          boundaryFunctional (O 1) Z (i₁ 1) (q₀ 1) (j₁ 1) N nS (hc₁ 1) (g₁ 1) (hb₁ 1))
    let graph : Cor.mk X ⟶ Cor.mk Z := ((graphFunctor k).map r : Cor.mk X ⟶ Cor.mk Z)
    target - correction - graph =
      PrincipalOrderCorrespondence.correspondence q jT₁ W hW₁ R hR gT₁ hbT₁ := by
  let I : LineBundle (C₀ 0) := ⟨Scheme.Hom.idealModule γ, hI⟩
  let A := tensorLineBundle (C₀ 0) M (dualLineBundle (C₀ 0) I)
  let af := sectionDualFunctional (C₀ 0) A aS
  let bf := sectionDualFunctional (C₀ 0) M bS
  let cf := sectionDualFunctional (C₀ 0) A
    (twistedIdealSection (C₀ 0) I M (Scheme.Hom.idealInclusion γ) bS)
  dsimp only
  intro ham0 hbm0 ham1 hbm1 hai0 hbi0 hai1 hbi1 hpole hg
  let : IsIso ((Scheme.Modules.pullback (i₀ 0)).map af) :=
    sectionDualFunctional_pullback_map_isIso (i₀ 0) A aS
  let : IsIso ((Scheme.Modules.pullback (i₀ 0)).map bf) :=
    sectionDualFunctional_pullback_map_isIso (i₀ 0) M bS
  have hn := originalPair_norm_product X Y O α q jT C U B C₀ U₀ B₀ f i j w hw
    q₀ i₀ j₀ c v hv Hp γ hI δ hδ hq M aS bS N nS dS hc hc₀
    g hb g₀ hb₀ hgv φ hφ hnormal hfree W hW R hR hg
  let : IsIso ((Scheme.Modules.pullback (i₁ 0)).map af) :=
    sectionDualFunctional_pullback_map_isIso (i₁ 0) A aS
  let : IsIso ((Scheme.Modules.pullback (i₁ 0)).map bf) :=
    sectionDualFunctional_pullback_map_isIso (i₁ 0) M bS
  have ha := boundaryFunctional_comp_graph_of_open_extension (O 0) Z Y
    (i₁ 0) (i₀ 0) (q₀ 0) (j₁ 0) (j₀ 0) (v₁ 0) (hv₁ 0)
    (dualLineBundle (C₀ 0) A) af (hc₁ 0) (hc₀ 0)
    (g₁ 0) (hb₁ 0) (g₀ 0) (hb₀ 0) u (hgu₁ 0)
  have hb' := boundaryFunctional_comp_graph_of_open_extension (O 0) Z Y
    (i₁ 0) (i₀ 0) (q₀ 0) (j₁ 0) (j₀ 0) (v₁ 0) (hv₁ 0)
    (dualLineBundle (C₀ 0) M) bf (hc₁ 0) (hc₀ 0)
    (g₁ 0) (hb₁ 0) (g₀ 0) (hb₀ 0) u (hgu₁ 0)
  have hnS := boundaryFunctional_comp_graph_of_open_extension (O 1) Z Y
    (i₁ 1) (i₀ 1) (q₀ 1) (j₁ 1) (j₀ 1) (v₁ 1) (hv₁ 1)
    N nS (hc₁ 1) (hc₀ 1) (g₁ 1) (hb₁ 1) (g₀ 1) (hb₀ 1) u (hgu₁ 1)
  have hdS := boundaryFunctional_comp_graph_of_open_extension (O 1) Z Y
    (i₁ 1) (i₀ 1) (q₀ 1) (j₁ 1) (j₀ 1) (v₁ 1) (hv₁ 1)
    N dS (hc₁ 1) (hc₀ 1) (g₁ 1) (hb₁ 1) (g₀ 1) (hb₀ 1) u (hgu₁ 1)
  have hext₀ := parameter_pair_extension (D := Cor k)
    (X := Cor.mk X) (O := Cor.mk (O 0)) (Y := Cor.mk Z) (Z := Cor.mk Y)
    ((graphFunctor k).map (α 0)) ha hb'
  have hext₁ := parameter_pair_extension (D := Cor k)
    (X := Cor.mk X) (O := Cor.mk (O 1)) (Y := Cor.mk Z) (Z := Cor.mk Y)
    ((graphFunctor k).map (α 1)) hdS hnS
  have hgraph : ((graphFunctor k).map r : Cor.mk X ⟶ Cor.mk Z) ≫
      (graphFunctor k).map u = (graphFunctor k).map (α 0 ≫ φ) := by
    rw [← Functor.map_comp, hru]
  have hprincipal := PrincipalOrderCorrespondence.correspondence_comp_graph_of_open_extension
    X Z Y q jT₁ jT vT hvT W hW₁ hW R hR gT₁ hbT₁ g
      (by simpa only [Category.assoc] using hb) u hguT₁
  exact product_eq_of_postcomp_eq (D := Cor k)
    (X := Cor.mk X) (Y := Cor.mk Z) (Z := Cor.mk Y)
    (f := (graphFunctor k).map u)
    (comp_open_graph_injective (X := X) (Y := Z) (Z := Y) u)
    hext₀ hext₁ hgraph hprincipal hn

end Motivic.Cor
