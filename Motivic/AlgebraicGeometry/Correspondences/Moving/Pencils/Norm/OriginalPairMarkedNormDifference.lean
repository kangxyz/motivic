/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.Norm.OriginalPairNormDifference
public import Motivic.Transfers.Presheaf.Actions.Pencils.CorrectionBoundary
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.PrincipalOrderOpenExtension
public import Motivic.AlgebraicGeometry.Correspondences.Support.OpenTargetFaithfulness


/-! # Return the same original parameter-changed pairs to the marked complement

Graph cancellation takes place on the enlarged curves. Only the two original
numerator and pole sections are extended from the marked complement, before
left composition by the original parameter maps. No graph-pole unit on the
marked boundary and no equality of correspondence actions is assumed.
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

private theorem difference_eq_of_postcomp_eq {D : Type*} [Category D] [Preadditive D]
    {X Y Z : D} {f : Y ⟶ Z} {a₀ a₁ p : X ⟶ Y} {b₀ b₁ q : X ⟶ Z}
    (hf : Function.Injective (fun a : X ⟶ Y => a ≫ f))
    (h₀ : a₀ ≫ f = b₀) (h₁ : a₁ ≫ f = b₁) (hp : p ≫ f = q)
    (hbig : b₀ - b₁ = q) : a₀ - a₁ = p := by
  apply hf
  dsimp only
  rw [Preadditive.sub_comp, h₀, h₁, hp, hbig]


/-- The normalized norm quotient compares both original pairs on the marked
complement. Parameter maps and section choices remain unchanged throughout. -/
theorem originalPair_norm_difference_marked
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
    (r : Γ(T, W)) (hr : IsUnit r)
    (Z : SmoothSite (Spec (.of k))) (u : Z ⟶ Y) [IsOpenImmersion u.left]
    (U₁ B₁ : Fin 2 → Scheme.{u}) (i₁ : ∀ t, B₁ t ⟶ C₀ t)
    (j₁ : ∀ t, U₁ t ⟶ C₀ t) [∀ t, IsOpenImmersion (j₁ t)]
    [∀ t, (U₁ t).IsQuasiAffine]
    [∀ t, SmoothOfRelativeDimension 1 (j₁ t ≫ q₀ t)]
    (v₁ : ∀ t, U₁ t ⟶ U₀ t) (hv₁ : ∀ t, v₁ t ≫ j₀ t = j₁ t)
    (hc₁ : ∀ t (x : C₀ t), x ∈ Set.range (j₁ t) ∨ x ∈ Set.range (i₁ t))
    [∀ t, IsIso (pullbackSectionMap (i₁ t) (aS t))]
    [∀ t, IsIso (pullbackSectionMap (i₁ t) (bS t))]
    (g₁ : ∀ t, U₁ t ⟶ Z.left)
    (hb₁ : ∀ t, (j₁ t ≫ q₀ t) ≫ (O t).hom = g₁ t ≫ Z.hom)
    (hgu₁ : ∀ t, g₁ t ≫ u.left = v₁ t ≫ g₀ t)
    {V₁ : Scheme.{u}} (jT₁ : V₁ ⟶ T) [IsOpenImmersion jT₁]
    [V₁.IsQuasiAffine] [SmoothOfRelativeDimension 1 (jT₁ ≫ q)]
    (vT : V₁ ⟶ V) (hvT : vT ≫ jT = jT₁)
    (hW₁ : (Set.range jT₁)ᶜ ⊆ (W : Set T))
    (gT₁ : V₁ ⟶ Z.left) (hbT₁ : jT₁ ≫ q ≫ X.hom = gT₁ ≫ Z.hom)
    (hguT₁ : gT₁ ≫ u.left = vT ≫ g) :
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
      (boundarySection (O t) Z (i₁ t) (q₀ t) (j₁ t) (A t) (hc₁ t) (g₁ t) (hb₁ t) (aS t) -
        boundarySection (O t) Z (i₁ t) (q₀ t) (j₁ t) (M t) (hc₁ t) (g₁ t) (hb₁ t) (bS t))
    d 0 - d 1 = PrincipalOrderCorrespondence.correspondence q jT₁ W hW₁ r hr gT₁ hbT₁ := by
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
  have hn := originalPair_norm_difference X Y O α q jT C U B C₀ U₀ B₀ f i j w hw
    q₀ i₀ j₀ c v hv Hp γ hI δ hδ hq M aS bS hc hc₀ g hb g₀ hb₀ hgv φ hφ
    hgraphs hnormal hfree W hW r hr hg
  let : ∀ t, IsIso ((Scheme.Modules.pullback (i₀ t)).map (af t)) :=
    fun t => sectionDualFunctional_pullback_map_isIso (i₀ t) (A t) (aS t)
  let : ∀ t, IsIso ((Scheme.Modules.pullback (i₁ t)).map (af t)) :=
    fun t => sectionDualFunctional_pullback_map_isIso (i₁ t) (A t) (aS t)
  let : ∀ t, IsIso ((Scheme.Modules.pullback (i₀ t)).map (bf t)) :=
    fun t => sectionDualFunctional_pullback_map_isIso (i₀ t) (M t) (bS t)
  let : ∀ t, IsIso ((Scheme.Modules.pullback (i₁ t)).map (bf t)) :=
    fun t => sectionDualFunctional_pullback_map_isIso (i₁ t) (M t) (bS t)
  have ha (t : Fin 2) := boundaryFunctional_comp_graph_of_open_extension (O t) Z Y
    (i₁ t) (i₀ t) (q₀ t) (j₁ t) (j₀ t) (v₁ t) (hv₁ t)
    (dualLineBundle (C₀ t) (A t)) (af t) (hc₁ t) (hc₀ t)
    (g₁ t) (hb₁ t) (g₀ t) (hb₀ t) u (hgu₁ t)
  have hb' (t : Fin 2) := boundaryFunctional_comp_graph_of_open_extension (O t) Z Y
    (i₁ t) (i₀ t) (q₀ t) (j₁ t) (j₀ t) (v₁ t) (hv₁ t)
    (dualLineBundle (C₀ t) (M t)) (bf t) (hc₁ t) (hc₀ t)
    (g₁ t) (hb₁ t) (g₀ t) (hb₀ t) u (hgu₁ t)
  have hext (t : Fin 2) :
      ((graphFunctor k).map (α t) ≫
        (boundarySection (O t) Z (i₁ t) (q₀ t) (j₁ t) (A t) (hc₁ t) (g₁ t) (hb₁ t) (aS t) -
          boundarySection (O t) Z (i₁ t) (q₀ t) (j₁ t) (M t) (hc₁ t) (g₁ t) (hb₁ t) (bS t))) ≫
        (graphFunctor k).map u =
      (graphFunctor k).map (α t) ≫
        (boundarySection (O t) Y (i₀ t) (q₀ t) (j₀ t) (A t) (hc₀ t) (g₀ t) (hb₀ t) (aS t) -
          boundarySection (O t) Y (i₀ t) (q₀ t) (j₀ t) (M t) (hc₀ t) (g₀ t) (hb₀ t) (bS t)) := by
    have halg (a b : Cor.mk (O t) ⟶ Cor.mk Z) (f : Cor.mk X ⟶ Cor.mk (O t))
        (g : Cor.mk Z ⟶ Cor.mk Y) :
        (f ≫ (a - b)) ≫ g = f ≫ (a ≫ g - b ≫ g) := by
      rw [Category.assoc, Preadditive.sub_comp]
    erw [halg]
    dsimp only [boundarySection]
    erw [ha t, hb' t]
  have hprincipal := PrincipalOrderCorrespondence.correspondence_comp_graph_of_open_extension
    X Z Y q jT₁ jT vT hvT W hW₁ hW r hr gT₁ hbT₁ g
      (by simpa only [Category.assoc] using hb) u hguT₁
  exact difference_eq_of_postcomp_eq (D := Cor k)
    (X := Cor.mk X) (Y := Cor.mk Z) (Z := Cor.mk Y)
    (f := (graphFunctor k).map u)
    (comp_open_graph_injective (X := X) (Y := Z) (Z := Y) u)
    (hext 0) (hext 1) hprincipal hn

end Motivic.Cor
