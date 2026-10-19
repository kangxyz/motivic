/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.Norm.GraphTwistedPoleCorrespondence
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.BoundaryFunctional.CartesianBaseChange


/-! # The original graph-pole identity under parameter pullback

The pulled pole remains the literal pullback of the original functional. Its
graph identity is obtained by left composition of the original identity, not
by choosing another graph line or another section on the new compactification.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

universe u
namespace Motivic.Cor

/-- Pull back the original whole graph-pole identity through the actual retained
Cartesian square. All boundary units concern the enlarged infinity boundaries. -/
theorem boundaryFunctional_pulled_graphPole_eq_graph_add
    {k : Type u} [Field k] (X X' Y : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsAffine X'.left]
    {C B U C' B' U' : Scheme.{u}} (i : B ⟶ C) (q : C ⟶ X.left) [IsProper q]
    (j : U ⟶ C) [IsOpenImmersion j] [U.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (γ : X.left ⟶ C) [IsClosedImmersion γ]
    (hI : IsLocallyRankOne C (Scheme.Hom.idealModule γ))
    (δ : X.left ⟶ U) (hδ : δ ≫ j = γ) (hq : γ ≫ q = 𝟙 X.left)
    (M : LineBundle C) (bS : SheafOfModules.unit C.ringCatSheaf ⟶ M.val)
    [IsIso (pullbackSectionMap i bS)]
    [IsIso ((Scheme.Modules.pullback i).map (Scheme.Hom.idealInclusion γ))]
    [IsIso (pullbackSectionMap i
      (twistedIdealSection C ⟨Scheme.Hom.idealModule γ, hI⟩ M
        (Scheme.Hom.idealInclusion γ) bS))]
    (hc : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range i)
    (g : U ⟶ Y.left) (φ : X ⟶ Y) (hg : δ ≫ g = φ.left)
    (hb : (j ≫ q) ≫ X.hom = g ≫ Y.hom)
    (i' : B' ⟶ C') (q' : C' ⟶ X'.left) [IsProper q']
    (j' : U' ⟶ C') [IsOpenImmersion j'] [U'.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j' ≫ q')]
    (c : C' ⟶ C) (v : U' ⟶ U) (hv : v ≫ j = j' ≫ c)
    (hc' : ∀ x : C', x ∈ Set.range j' ∨ x ∈ Set.range i')
    (α : X' ⟶ X) [Flat α.left]
    (H : IsPullback v (j' ≫ q') (j ≫ q) α.left) :
    let L := tensorLineBundle C M (dualLineBundle C ⟨Scheme.Hom.idealModule γ, hI⟩)
    let cS := twistedIdealSection C ⟨Scheme.Hom.idealModule γ, hI⟩ M
      (Scheme.Hom.idealInclusion γ) bS
    let cf := sectionDualFunctional C L cS
    let bf := sectionDualFunctional C M bS
    ∀ [IsIso ((Scheme.Modules.pullback i').map (Hom.pullbackToUnit cf c))]
      [IsIso ((Scheme.Modules.pullback i').map (Hom.pullbackToUnit bf c))],
    let hb' : (j' ≫ q') ≫ X'.hom = (v ≫ g) ≫ Y.hom := by
      calc
        (j' ≫ q') ≫ X'.hom = ((j' ≫ q') ≫ α.left) ≫ X.hom := by
          simp only [Category.assoc, MorphismProperty.Over.w]
        _ = (v ≫ (j ≫ q)) ≫ X.hom := by rw [← H.w]
        _ = (v ≫ g) ≫ Y.hom := by rw [Category.assoc, hb, Category.assoc]
    boundaryFunctional X' Y i' q' j' (pullbackLineBundle c (dualLineBundle C L))
      (Hom.pullbackToUnit cf c) hc' (v ≫ g) hb' =
      @Add.add (Cor.mk X' ⟶ Cor.mk Y) inferInstance ((graphFunctor k).map (α ≫ φ))
        (boundaryFunctional X' Y i' q' j' (pullbackLineBundle c (dualLineBundle C M))
          (Hom.pullbackToUnit bf c) hc' (v ≫ g) hb') := by
  let L := tensorLineBundle C M (dualLineBundle C ⟨Scheme.Hom.idealModule γ, hI⟩)
  let cS := twistedIdealSection C ⟨Scheme.Hom.idealModule γ, hI⟩ M
    (Scheme.Hom.idealInclusion γ) bS
  let cf := sectionDualFunctional C L cS
  let bf := sectionDualFunctional C M bS
  dsimp only
  intro hci hbi
  have := sectionDualFunctional_pullback_map_isIso i L cS
  have := sectionDualFunctional_pullback_map_isIso i M bS
  have he := boundarySection_twistedIdeal_eq_graph_add X Y i q j γ hI δ hδ hq
    M bS hc g φ hg hb
  have hleft := congrArg (fun z : Cor.mk X ⟶ Cor.mk Y => (graphFunctor k).map α ≫ z) he
  change _ = (graphFunctor k).map α ≫ ((graphFunctor k).map φ + _) at hleft
  erw [Preadditive.comp_add, ← Functor.map_comp] at hleft
  dsimp only [boundarySection] at hleft
  erw [graph_boundaryFunctional_of_cartesian X' X Y i q j i' q' j' c v hv
      (dualLineBundle C L) cf hc hc' g hb α H,
    graph_boundaryFunctional_of_cartesian X' X Y i q j i' q' j' c v hv
      (dualLineBundle C M) bf hc hc' g hb α H] at hleft
  exact hleft

end Motivic.Cor
