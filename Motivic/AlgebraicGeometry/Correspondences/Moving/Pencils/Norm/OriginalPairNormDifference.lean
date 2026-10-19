/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.BoundaryFunctional.NormCommuting
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.Norm.GraphPoleCartesianBaseChange
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.TwistedIdealRegularity


/-! # Norm comparison for the same original pairs under parameter change

Both pairs remain the original sections. Their compactified pullbacks are
literal module maps, not duals of replacement sections. The intended parameter
maps are the identity for the source pair and the original etale map for the
target pair. Graph cancellation uses an equality of the actual site maps.
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

/-- The actual norm quotient compares left graph compositions of the two
original numerator-minus-pole pairs. All omitted-boundary units concern the
enlarged curves; no graph-pole marked-boundary unit is required. -/
theorem originalPair_norm_difference
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
    (c : ∀ t, C t ⟶ C₀ t) [∀ t, Flat (c t)]
    (v : ∀ t, U t ⟶ U₀ t) (hv : ∀ t, v t ≫ j₀ t = j t ≫ c t)
    (Hp : ∀ t, IsPullback (v t) (j t ≫ (f t ≫ q)) (j₀ t ≫ q₀ t) (α t).left)
    (γ : ∀ t, (O t).left ⟶ C₀ t) [∀ t, IsClosedImmersion (γ t)]
    (hI : ∀ t, IsLocallyRankOne (C₀ t) (Scheme.Hom.idealModule (γ t)))
    (δ : ∀ t, (O t).left ⟶ U₀ t) (hδ : ∀ t, δ t ≫ j₀ t = γ t)
    (hq : ∀ t, γ t ≫ q₀ t = 𝟙 (O t).left)
    (M : ∀ t, LineBundle (C₀ t))
    (aS : ∀ t, SheafOfModules.unit (C₀ t).ringCatSheaf ⟶
      (tensorLineBundle (C₀ t) (M t)
        (dualLineBundle (C₀ t) ⟨Scheme.Hom.idealModule (γ t), hI t⟩)).val)
    (bS : ∀ t, SheafOfModules.unit (C₀ t).ringCatSheaf ⟶ (M t).val)
    [∀ t, IsIso (pullbackSectionMap (i₀ t) (aS t))]
    [∀ t, IsIso (pullbackSectionMap (i₀ t) (bS t))]
    [∀ t, IsIso ((Scheme.Modules.pullback (i₀ t)).map (Scheme.Hom.idealInclusion (γ t)))]
    [∀ t, IsIso (pullbackSectionMap (i₀ t)
      (twistedIdealSection (C₀ t) ⟨Scheme.Hom.idealModule (γ t), hI t⟩ (M t)
        (Scheme.Hom.idealInclusion (γ t)) (bS t)))]
    [∀ t, Mono (sectionDualFunctional (C₀ t)
      (tensorLineBundle (C₀ t) (M t)
        (dualLineBundle (C₀ t) ⟨Scheme.Hom.idealModule (γ t), hI t⟩)) (aS t))]
    [∀ t, Mono (sectionDualFunctional (C₀ t) (M t) (bS t))]
    (hc : ∀ t (x : C t), x ∈ Set.range (j t) ∨ x ∈ Set.range (i t))
    (hc₀ : ∀ t (x : C₀ t), x ∈ Set.range (j₀ t) ∨ x ∈ Set.range (i₀ t))
    (g : V ⟶ Y.left) (hb : (jT ≫ q) ≫ X.hom = g ≫ Y.hom)
    (g₀ : ∀ t, U₀ t ⟶ Y.left)
    (hb₀ : ∀ t, (j₀ t ≫ q₀ t) ≫ (O t).hom = g₀ t ≫ Y.hom)
    (hgv : ∀ t, v t ≫ g₀ t = w t ≫ g)
    (φ : ∀ t, O t ⟶ Y) (hφ : ∀ t, δ t ≫ g₀ t = (φ t).left)
    (hgraphs : α 0 ≫ φ 0 = α 1 ≫ φ 1)
    (hnormal : ∀ (W : T.Opens), IsAffineOpen W → Nonempty W → IsIntegrallyClosed Γ(T, W))
    (hfree : ∀ t (x : T), ∃ (W : T.Opens) (hW : IsAffineOpen W), x ∈ W ∧
      (let : Algebra Γ(T, W) Γ(Limits.pullback (f t) hW.fromSpec, ⊤) :=
        (scalarMap (pullback.snd (f t) hW.fromSpec)).toAlgebra
       Module.Free Γ(T, W) Γ(Limits.pullback (f t) hW.fromSpec, ⊤)))
    (W : T.Opens) [Nonempty W] (hW : (Set.range jT)ᶜ ⊆ (W : Set T))
    (r : Γ(T, W)) (hr : IsUnit r) :
    let I := fun t => (⟨Scheme.Hom.idealModule (γ t), hI t⟩ : LineBundle (C₀ t))
    let A := fun t => tensorLineBundle (C₀ t) (M t) (dualLineBundle (C₀ t) (I t))
    let af := fun t => sectionDualFunctional (C₀ t) (A t) (aS t)
    let bf := fun t => sectionDualFunctional (C₀ t) (M t) (bS t)
    let cf := fun t => sectionDualFunctional (C₀ t) (A t)
      (twistedIdealSection (C₀ t) (I t) (M t) (Scheme.Hom.idealInclusion (γ t)) (bS t))
    let L := fun t => pullbackLineBundle (c t) (dualLineBundle (C₀ t) (A t))
    let ap := fun t => Hom.pullbackToUnit (af t) (c t)
    let cp := fun t => Hom.pullbackToUnit (cf t) (c t)
    let : ∀ t, Mono (Scheme.Hom.idealInclusion (γ t)) := fun t => Scheme.Hom.idealInclusionMono _
    let : ∀ t, Mono (cf t) := fun t => twistedIdealSection_mono
      (C₀ t) (I t) (M t) (Scheme.Hom.idealInclusion (γ t)) (bS t)
    let : ∀ t, Mono (ap t) := fun t => by
      dsimp only [ap, af, A, I, Hom.pullbackToUnit]
      infer_instance
    let : ∀ t, Mono (cp t) := fun t => by
      dsimp only [cp, Hom.pullbackToUnit]
      infer_instance
    ∀ [∀ t, IsIso ((Scheme.Modules.pullback (i t)).map (ap t))]
      [∀ t, IsIso ((Scheme.Modules.pullback (i t)).map (cp t))]
      [∀ t, IsIso ((Scheme.Modules.pullback (i t)).map (Hom.pullbackToUnit (bf t) (c t)))],
    T.germToFunctionField W r = Scheme.genericFiberLineRatioNorm (f 0) (L 0) (ap 0) (cp 0) /
      Scheme.genericFiberLineRatioNorm (f 1) (L 1) (ap 1) (cp 1) →
    let d := fun t => (graphFunctor k).map (α t) ≫
      (boundarySection (O t) Y (i₀ t) (q₀ t) (j₀ t) (A t) (hc₀ t) (g₀ t) (hb₀ t) (aS t) -
        boundarySection (O t) Y (i₀ t) (q₀ t) (j₀ t) (M t) (hc₀ t) (g₀ t) (hb₀ t) (bS t))
    d 0 - d 1 = PrincipalOrderCorrespondence.correspondence q jT W hW r hr g
      (by simpa only [Category.assoc] using hb) := by
  let I := fun t => (⟨Scheme.Hom.idealModule (γ t), hI t⟩ : LineBundle (C₀ t))
  let A := fun t => tensorLineBundle (C₀ t) (M t) (dualLineBundle (C₀ t) (I t))
  let af := fun t => sectionDualFunctional (C₀ t) (A t) (aS t)
  let bf := fun t => sectionDualFunctional (C₀ t) (M t) (bS t)
  let cf := fun t => sectionDualFunctional (C₀ t) (A t)
    (twistedIdealSection (C₀ t) (I t) (M t) (Scheme.Hom.idealInclusion (γ t)) (bS t))
  let L := fun t => pullbackLineBundle (c t) (dualLineBundle (C₀ t) (A t))
  let ap := fun t => Hom.pullbackToUnit (af t) (c t)
  let cp := fun t => Hom.pullbackToUnit (cf t) (c t)
  let : ∀ t, Mono (Scheme.Hom.idealInclusion (γ t)) := fun t => Scheme.Hom.idealInclusionMono _
  let : ∀ t, Mono (cf t) := fun t => twistedIdealSection_mono
    (C₀ t) (I t) (M t) (Scheme.Hom.idealInclusion (γ t)) (bS t)
  let : ∀ t, Mono (ap t) := fun t => by
    dsimp only [ap, af, A, I, Hom.pullbackToUnit]
    infer_instance
  let : ∀ t, Mono (cp t) := fun t => by
    dsimp only [cp, Hom.pullbackToUnit]
    infer_instance
  dsimp only
  intro hai hci hbi hg
  let : ∀ t, IsIso ((Scheme.Modules.pullback (i₀ t)).map (af t)) :=
    fun t => sectionDualFunctional_pullback_map_isIso (i₀ t) (A t) (aS t)
  let : ∀ t, IsIso ((Scheme.Modules.pullback (i₀ t)).map (bf t)) :=
    fun t => sectionDualFunctional_pullback_map_isIso (i₀ t) (M t) (bS t)
  have hn := boundaryFunctional_norm_difference_of_comm X Y q jT C U B f i j w hw L ap cp
    hc hnormal hfree W hW r hr hg g hb
  have hbase (t : Fin 2) : (j t ≫ (f t ≫ q)) ≫ X.hom = (w t ≫ g) ≫ Y.hom := by
    simpa only [← Category.assoc, hw t] using congrArg (w t ≫ ·) hb
  have hnum (t : Fin 2) := graph_boundaryFunctional_of_cartesian X (O t) Y
    (i₀ t) (q₀ t) (j₀ t) (i t) (f t ≫ q) (j t) (c t) (v t) (hv t)
    (dualLineBundle (C₀ t) (A t)) (af t) (hc₀ t) (hc t) (g₀ t) (hb₀ t) (α t) (Hp t)
  have hpole (t : Fin 2) := graph_boundaryFunctional_of_cartesian X (O t) Y
    (i₀ t) (q₀ t) (j₀ t) (i t) (f t ≫ q) (j t) (c t) (v t) (hv t)
    (dualLineBundle (C₀ t) (M t)) (bf t) (hc₀ t) (hc t) (g₀ t) (hb₀ t) (α t) (Hp t)
  have hgraph (t : Fin 2) := boundaryFunctional_pulled_graphPole_eq_graph_add
    (O t) X Y (i₀ t) (q₀ t) (j₀ t) (γ t) (hI t) (δ t) (hδ t) (hq t)
    (M t) (bS t) (hc₀ t) (g₀ t) (φ t) (hφ t) (hb₀ t)
    (i t) (f t ≫ q) (j t) (c t) (v t) (hv t) (hc t) (α t) (Hp t)
  simp only [hgv] at hnum hpole hgraph
  dsimp only [boundarySection]
  erw [Preadditive.comp_sub, Preadditive.comp_sub, hnum 0, hpole 0, hnum 1, hpole 1]
  dsimp only [L, ap, cp, cf, A, I] at hn
  erw [hgraph 0, hgraph 1, hgraphs] at hn
  have halg (a b c d g : Cor.mk X ⟶ Cor.mk Y) :
      (a - b) - (c - d) = (a - (g + b)) - (c - (g + d)) := by abel
  exact (halg _ _ _ _ _).trans hn

end Motivic.Cor
