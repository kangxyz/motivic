/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.BoundaryFunctional.NormCommuting
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.Norm.GraphPoleCartesianBaseChange


/-! # Original target and correction pairs with their product norm

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

private theorem original_product_eq {D : Type*} [Category D] [Preadditive D]
    {X A B Y : D} {u : X ⟶ A} {v : X ⟶ B} {a b : A ⟶ Y} {n d : B ⟶ Y}
    {a' b' c' n' d' g p : X ⟶ Y}
    (ha : u ≫ a = a') (hb : u ≫ b = b')
    (hn : v ≫ n = n') (hd : v ≫ d = d')
    (hc : c' = g + b') (hsum : (a' - c') + (n' - d') = p) :
    u ≫ (a - b) - v ≫ (d - n) - g = p := by
  rw [Preadditive.comp_sub, Preadditive.comp_sub, ha, hb, hd, hn]
  rw [hc] at hsum
  calc
    (a' - b') - (d' - n') - g = (a' - (g + b')) + (n' - d') := by abel
    _ = p := hsum

/-- The genuine product norm gives the original target-minus-correction-minus-
graph correspondence. The correction is `dS - nS`, not its negative. The unit
representative and its germ are geometric inputs on the same compactification. -/
theorem originalPair_norm_product
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
    (R : Γ(T, W)) (hR : IsUnit R) :
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
    let target : Cor.mk X ⟶ Cor.mk Y := ((graphFunctor k).map (α 0) : Cor.mk X ⟶ Cor.mk (O 0)) ≫
      (boundarySection (O 0) Y (i₀ 0) (q₀ 0) (j₀ 0) A (hc₀ 0) (g₀ 0) (hb₀ 0) aS -
        boundarySection (O 0) Y (i₀ 0) (q₀ 0) (j₀ 0) M (hc₀ 0) (g₀ 0) (hb₀ 0) bS)
    let correction : Cor.mk X ⟶ Cor.mk Y := ((graphFunctor k).map (α 1) : Cor.mk X ⟶ Cor.mk (O 1)) ≫
        (boundaryFunctional (O 1) Y (i₀ 1) (q₀ 1) (j₀ 1) N dS (hc₀ 1) (g₀ 1) (hb₀ 1) -
          boundaryFunctional (O 1) Y (i₀ 1) (q₀ 1) (j₀ 1) N nS (hc₀ 1) (g₀ 1) (hb₀ 1))
    let graph : Cor.mk X ⟶ Cor.mk Y := ((graphFunctor k).map (α 0 ≫ φ) : Cor.mk X ⟶ Cor.mk Y)
    target - correction - graph =
      PrincipalOrderCorrespondence.correspondence q jT W hW R hR g
        (by simpa only [Category.assoc] using hb) := by
  let I : LineBundle (C₀ 0) := ⟨Scheme.Hom.idealModule γ, hI⟩
  let A := tensorLineBundle (C₀ 0) M (dualLineBundle (C₀ 0) I)
  let af := sectionDualFunctional (C₀ 0) A aS
  let bf := sectionDualFunctional (C₀ 0) M bS
  let cf := sectionDualFunctional (C₀ 0) A
    (twistedIdealSection (C₀ 0) I M (Scheme.Hom.idealInclusion γ) bS)
  let L₀ : ∀ t, LineBundle (C₀ t) := Fin.cases (dualLineBundle (C₀ 0) A) (Fin.cases N (fun t =>
      Fin.elim0 t))
  let a₀ : ∀ t, (L₀ t).val ⟶ SheafOfModules.unit (C₀ t).ringCatSheaf :=
    Fin.cases af (Fin.cases nS (fun t => Fin.elim0 t))
  let b₀ : ∀ t, (L₀ t).val ⟶ SheafOfModules.unit (C₀ t).ringCatSheaf :=
    Fin.cases cf (Fin.cases dS (fun t => Fin.elim0 t))
  let L := fun t => pullbackLineBundle (c t) (L₀ t)
  let ap := fun t => Hom.pullbackToUnit (a₀ t) (c t)
  let bp := fun t => Hom.pullbackToUnit (b₀ t) (c t)
  dsimp only
  intro ham0 hbm0 ham1 hbm1 hai0 hbi0 hai1 hbi1 hpole hg
  let : ∀ t, Mono (ap t) := Fin.cases ham0 (Fin.cases ham1 (fun t => Fin.elim0 t))
  let : ∀ t, Mono (bp t) := Fin.cases hbm0 (Fin.cases hbm1 (fun t => Fin.elim0 t))
  let : ∀ t, IsIso ((Scheme.Modules.pullback (i t)).map (ap t)) :=
    Fin.cases hai0 (Fin.cases hai1 (fun t => Fin.elim0 t))
  let : ∀ t, IsIso ((Scheme.Modules.pullback (i t)).map (bp t)) :=
    Fin.cases hbi0 (Fin.cases hbi1 (fun t => Fin.elim0 t))
  let : IsIso ((Scheme.Modules.pullback (i₀ 0)).map af) :=
    sectionDualFunctional_pullback_map_isIso (i₀ 0) A aS
  let : IsIso ((Scheme.Modules.pullback (i₀ 0)).map bf) :=
    sectionDualFunctional_pullback_map_isIso (i₀ 0) M bS
  let : IsIso ((Scheme.Modules.pullback (i 0)).map (Hom.pullbackToUnit af (c 0))) := hai0
  let : IsIso ((Scheme.Modules.pullback (i 0)).map (Hom.pullbackToUnit cf (c 0))) := hbi0
  let : IsIso ((Scheme.Modules.pullback (i 1)).map (Hom.pullbackToUnit nS (c 1))) := hai1
  let : IsIso ((Scheme.Modules.pullback (i 1)).map (Hom.pullbackToUnit dS (c 1))) := hbi1
  have hn := boundaryFunctional_norm_sum_of_comm X Y q jT C U B f i j w hw L ap bp
    hc hnormal hfree W hW R hR hg g hb
  have hnum := graph_boundaryFunctional_of_cartesian X (O 0) Y
    (i₀ 0) (q₀ 0) (j₀ 0) (i 0) (f 0 ≫ q) (j 0) (c 0) (v 0) (hv 0)
    (dualLineBundle (C₀ 0) A) af (hc₀ 0) (hc 0) (g₀ 0) (hb₀ 0) (α 0) (Hp 0)
  have hp := graph_boundaryFunctional_of_cartesian X (O 0) Y
    (i₀ 0) (q₀ 0) (j₀ 0) (i 0) (f 0 ≫ q) (j 0) (c 0) (v 0) (hv 0)
    (dualLineBundle (C₀ 0) M) bf (hc₀ 0) (hc 0) (g₀ 0) (hb₀ 0) (α 0) (Hp 0)
  have hnS := graph_boundaryFunctional_of_cartesian X (O 1) Y
    (i₀ 1) (q₀ 1) (j₀ 1) (i 1) (f 1 ≫ q) (j 1) (c 1) (v 1) (hv 1)
    N nS (hc₀ 1) (hc 1) (g₀ 1) (hb₀ 1) (α 1) (Hp 1)
  have hdS := graph_boundaryFunctional_of_cartesian X (O 1) Y
    (i₀ 1) (q₀ 1) (j₀ 1) (i 1) (f 1 ≫ q) (j 1) (c 1) (v 1) (hv 1)
    N dS (hc₀ 1) (hc 1) (g₀ 1) (hb₀ 1) (α 1) (Hp 1)
  have hgraph := boundaryFunctional_pulled_graphPole_eq_graph_add
    (O 0) X Y (i₀ 0) (q₀ 0) (j₀ 0) γ hI δ hδ hq M bS (hc₀ 0)
    (g₀ 0) φ hφ (hb₀ 0) (i 0) (f 0 ≫ q) (j 0) (c 0) (v 0) (hv 0)
    (hc 0) (α 0) (Hp 0)
  simp only [hgv] at hnum hp hnS hdS hgraph
  exact original_product_eq (D := Cor k) (X := Cor.mk X) (A := Cor.mk (O 0))
    (B := Cor.mk (O 1)) (Y := Cor.mk Y) hnum hp hnS hdS hgraph hn

end Motivic.Cor
