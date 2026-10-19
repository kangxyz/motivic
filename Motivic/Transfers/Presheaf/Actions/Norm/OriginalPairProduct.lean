/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.Norm.OriginalPairMarkedNormProduct
public import Motivic.Transfers.Presheaf.Actions.Principal.Open


/-! # HI action of the original product-norm comparison

The actual marked-complement correspondence comparison feeds the principal
homotopy on the same open and unit representative. The correction remains
its original denominator-minus-numerator pair and the graph is the actual
small-target map. Neither a correspondence identity nor an action identity
is supplied as a hypothesis.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open AlgebraicGeometry.FiniteSchemeNormBaseChange
open Motivic.Cor
universe v u
namespace Motivic.PresheafWithTransfers

/-- On an ordinary HI presheaf with transfers, the original target action is
the original correction action plus the actual small graph action. The genuine
full boundary and its value-one condition remain explicit geometric inputs. -/
theorem transfer_originalPair_norm_product
    {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
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
    {V₁ : Scheme.{u}} [IsNoetherian V₁] (jT₁ : V₁ ⟶ T) [IsOpenImmersion jT₁]
    [V₁.IsQuasiAffine] [SmoothOfRelativeDimension 1 (jT₁ ≫ q)]
    (vT : V₁ ⟶ V) (hvT : vT ≫ jT = jT₁)
    (hW₁ : (Set.range jT₁)ᶜ ⊆ (W : Set T))
    (gT₁ : V₁ ⟶ Z.left) (hbT₁ : jT₁ ≫ q ≫ X.hom = gT₁ ≫ Z.hom)
    (hguT₁ : gT₁ ≫ u.left = vT ≫ g)
    {E : Scheme.{u}} (b : E ⟶ W.toScheme) [Nonempty E]
    (hcover : (Set.range jT₁)ᶜ ⊆ Set.range (b ≫ W.ι))
    (hboundary : b.appTop (W.topIso.inv R) = 1) :
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
    P.transfer target = P.transfer correction + P.transfer graph := by
  let I : LineBundle (C₀ 0) := ⟨Scheme.Hom.idealModule γ, hI⟩
  let A := tensorLineBundle (C₀ 0) M (dualLineBundle (C₀ 0) I)
  let af := sectionDualFunctional (C₀ 0) A aS
  let bf := sectionDualFunctional (C₀ 0) M bS
  let cf := sectionDualFunctional (C₀ 0) A
    (twistedIdealSection (C₀ 0) I M (Scheme.Hom.idealInclusion γ) bS)
  dsimp only
  intro ham0 hbm0 ham1 hbm1 hai0 hbi0 hai1 hbi1 hpole hg
  have hn := Cor.originalPair_norm_product_marked X Y O α q jT C U B C₀ U₀ B₀
    f i j w hw q₀ i₀ j₀ c v hv Hp γ hI δ hδ hq M aS bS N nS dS hc hc₀
    g hb g₀ hb₀ hgv φ hφ hnormal hfree W hW R hR Z u U₁ B₁ i₁ j₁ v₁ hv₁
    hc₁ g₁ hb₁ hgu₁ r hru jT₁ vT hvT hW₁ gT₁ hbT₁ hguT₁ hg
  have hzero := transfer_principalOrder_open_eq_zero P hP X Z q jT₁ W R hR
    b hcover hboundary gT₁ hbT₁
  have he := congrArg P.transfer hn
  rw [transfer_sub, transfer_sub, sub_sub] at he
  exact sub_eq_zero.mp (he.trans hzero)

end Motivic.PresheafWithTransfers
