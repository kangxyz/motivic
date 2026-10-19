/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Graph.Frames.OriginalTriangle
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.AffineClosedTriangle
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.DiagonalBoundary

/-!
# The norm ideal of the original graph on an actual open chart

Both ideal frames are transported from the original fixed frames through the
native Cartesian ideal maps. The same-domain graph triangle constructs the
quotient equivalence internally. Freeness is required only for this chart's
original finite section algebra, not for a larger common neighborhood.


Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.OpenGraphTriangle`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.FlatChartIdealCoordinate`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- The canonical ideal comparison for an actual flat Cartesian chart. -/
def flatChartIdealIso {D D' X Y : Scheme.{u}}
    (i : D ⟶ X) (i' : D' ⟶ Y) (v : Y ⟶ X) (a : D' ⟶ D)
    (H : IsPullback a i' i v) [IsClosedImmersion i] [IsClosedImmersion i'] [Flat v]
    (hI : IsLocallyRankOne X (idealModule i)) :
    (Modules.pullback v).obj (idealModule i) ≅ idealModule i' := by
  let := lineBundle_isLocallyFree X (⟨idealModule i, hI⟩ : LineBundle X)
  have := idealPullbackMap_isIso_of_flat_ambient i i' v a H.w H
  exact asIso (idealPullbackMap i i' v a H.w)

/-- The chart frame is the GIVEN pulled frame through the actual ideal comparison,
not an independently chosen trivialization of the restricted graph. -/
def flatChartIdealTopFrame {D D' X Y : Scheme.{u}}
    (i : D ⟶ X) (i' : D' ⟶ Y) (v : Y ⟶ X) (a : D' ⟶ D)
    (H : IsPullback a i' i v) [IsClosedImmersion i] [IsClosedImmersion i'] [Flat v]
    (hI : IsLocallyRankOne X (idealModule i))
    (e : (Modules.pullback v).obj (idealModule i) ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (idealModule i').over ⊤ ≅ SheafOfModules.unit (Y.ringCatSheaf.over ⊤) :=
  (SheafOfModules.overFunctor Y.ringCatSheaf ⊤).mapIso
    ((flatChartIdealIso i i' v a H hI).symm ≪≫ e)

variable {S C X T : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  (f : C ⟶ X) [IsFinite f] (j : T ⟶ C)

/-- The original source graph is closed because its projection is separated. -/
theorem compactificationGraph_closed_of_finite :
    IsClosedImmersion (compactificationGraph (f ≫ q) j) := by
  have : IsClosedImmersion (compactificationGraph (f ≫ q) j ≫ pullback.fst _ _) := by
    simp only [compactificationGraph, pullback.lift_fst]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst _ _)

omit [IsSeparated q] [IsFinite f] in
/-- The target graph square on the constructed common domain is actually Cartesian. -/
theorem graphChartTarget_isPullback {W : Scheme.{u}}
    (w : W ⟶ pullback (j ≫ f ≫ q) q) :
    IsPullback
      ((graphChartDomainIso q f j w).hom ≫ pullback.fst (targetCompactificationGraph q f j) w)
      ((graphChartDomainIso q f j w).hom ≫ pullback.snd (targetCompactificationGraph q f j) w)
      (targetCompactificationGraph q f j) w := by
  apply IsPullback.of_iso_pullback _ (graphChartDomainIso q f j w) rfl rfl
  constructor
  simp only [Category.assoc, pullback.condition]

/-- Original fixed ideal frames on one affine free chart give the actual norm
ideal equality. No quotient isomorphism or independent graph generator is supplied. -/
theorem span_norm_originalGraph_chart
    {W : Scheme.{u}} [IsAffine W]
    (w : W ⟶ pullback (j ≫ f ≫ q) q) [IsOpenImmersion w]
    (hB : IsLocallyRankOne _ (idealModule (compactificationGraph (f ≫ q) j)))
    (hA : IsLocallyRankOne _ (idealModule (targetCompactificationGraph q f j)))
    (eB : (Modules.pullback (pullback.fst (graphProductMap q f j) w)).obj
        (idealModule (compactificationGraph (f ≫ q) j)) ≅
      SheafOfModules.unit (pullback (graphProductMap q f j) w).ringCatSheaf)
    (eA : (Modules.pullback w).obj (idealModule (targetCompactificationGraph q f j)) ≅
      SheafOfModules.unit W.ringCatSheaf) :
    let p := graphProductMap q f j
    let iB := pullback.snd (compactificationGraph (f ≫ q) j) (pullback.fst p w)
    let iA := (graphChartDomainIso q f j w).hom ≫ pullback.snd (targetCompactificationGraph q f j) w
    let aA := (graphChartDomainIso q f j w).hom ≫ pullback.fst (targetCompactificationGraph q f j) w
    let := compactificationGraph_closed_of_finite q f j
    let EB := flatChartIdealTopFrame (compactificationGraph (f ≫ q) j) iB (pullback.fst p w)
      (pullback.fst (compactificationGraph (f ≫ q) j) (pullback.fst p w))
      (IsPullback.of_hasPullback _ _) hB eB
    let EA := flatChartIdealTopFrame (targetCompactificationGraph q f j) iA w aA
      (graphChartTarget_isPullback q f j w) hA eA
    let : Algebra Γ(W, ⊤) Γ(pullback p w, ⊤) := (pullback.snd p w).appTop.hom.toAlgebra
    ∀ [Module.Free Γ(W, ⊤) Γ(pullback p w, ⊤)],
      Ideal.span {Algebra.norm Γ(W, ⊤) (idealFrameScalar iB ⊤ EB)} =
        Ideal.span {idealFrameScalar iA ⊤ EA} := by
  dsimp only
  let := compactificationGraph_closed_of_finite q f j
  let p := graphProductMap q f j
  let : Algebra Γ(W, ⊤) Γ(pullback p w, ⊤) := (pullback.snd p w).appTop.hom.toAlgebra
  intro hfree
  let := hfree
  let iB := pullback.snd (compactificationGraph (f ≫ q) j) (pullback.fst p w)
  let iA := (graphChartDomainIso q f j w).hom ≫ pullback.snd (targetCompactificationGraph q f j) w
  have hBi : IsLocallyRankOne _ (idealModule iB) :=
    isLocallyRankOne_of_iso _
      (flatChartIdealIso (compactificationGraph (f ≫ q) j) iB (pullback.fst p w)
        (pullback.fst _ _) (IsPullback.of_hasPullback _ _) hB)
      (pullback_locallyRankOne _ _ hB)
  have hAi : IsLocallyRankOne _ (idealModule iA) :=
    isLocallyRankOne_of_iso _
      (flatChartIdealIso (targetCompactificationGraph q f j) iA w
        ((graphChartDomainIso q f j w).hom ≫ pullback.fst _ _)
        (graphChartTarget_isPullback q f j w) hA)
      (pullback_locallyRankOne _ _ hA)
  exact span_norm_idealFrameScalar_eq (pullback.snd p w) iB iA
    (graphChart_triangle q f j w) hBi hAi _ _

end AlgebraicGeometry.Scheme.Hom
