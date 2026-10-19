/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.CompactificationBoundaryFrame
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.InfinityBoundaryIdeal
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.IdealFrameBoundaryScalar

/-! # Actual marked and infinity ideal-functional scalar values

The marked scalar keeps the given target ideal frame. It is not silently
normalized to a polynomial coordinate. The infinity value restricts along an
actual scheme map, so a nonreduced residual component must genuinely factor
through the supplied full infinity boundary.


Intended upstream module: `Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.GraphScalar`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.GraphRegular`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- The original marked ideal frame has exactly the supplied target-frame scalar. -/
theorem relativeCompactificationBoundaryFrame_scalar
    {S X Y Z C : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
    [SmoothOfRelativeDimension 1 q] (qC : C ⟶ S) [IsSeparated qC]
    (j : Y ⟶ C) [IsOpenImmersion j] (p : Y ⟶ X) [Flat p]
    (hq : j ≫ qC = p ≫ q) (z : Z ⟶ X) (s : Z ⟶ Y) (h : s ≫ p = z)
    (H : IsPullback s (𝟙 _) p z)
    (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
      idealModule (boundaryGraphTarget q z)) :
    (show Γ(pullback (j ≫ qC) (s ≫ j ≫ qC), ⊤) from Modules.Hom.app
      ((relativeCompactificationBoundaryFrame q qC j p hq z s h H e).hom ≫
        Modules.Hom.pullbackToUnit (idealInclusion (compactificationGraph qC j))
          (graphBoundaryRestriction qC j s)) ⊤ (1 : Γ(pullback (j ≫ qC) (s ≫ j ≫ qC), ⊤))) =
      ((relativeBoundaryProductIso q qC j p hq z s h).hom ≫
        boundaryProductMap q p z).appTop
          (Modules.Hom.app (e.hom ≫ idealInclusion (boundaryGraphTarget q z)) ⊤
            (1 : Γ(pullback q (z ≫ q), ⊤))) := by
  rw [relativeCompactificationBoundaryFrame_coordinate,
    unitEndomorphismPullback_app_one]

/-- The canonical infinity IDEAL frame has value one after restriction along
any actual residual map into the full infinity product. -/
theorem infinityIdealFrame_residual_scalar
    {S C Y D E : Scheme.{u}} (q : C ⟶ S) [IsSeparated q]
    (j : Y ⟶ C) [IsOpenImmersion j] (d : D ⟶ C)
    (h : Disjoint (Set.range j) (Set.range d))
    (r : E ⟶ pullback (pullback.snd (j ≫ q) q) d) :
    let φ := Modules.Hom.pullbackToUnit (idealInclusion (compactificationGraph q j))
      (infinityProductMap q j d)
    let := infinity_pullbackIdealInclusion_isIso q j d h
    (show Γ(E, ⊤) from Modules.Hom.app
      (unitEndomorphismPullback r ((asIso φ).inv ≫ φ)) ⊤ (1 : Γ(E, ⊤))) = 1 := by
  dsimp only
  have := infinity_pullbackIdealInclusion_isIso q j d h
  let φ := Modules.Hom.pullbackToUnit (idealInclusion (compactificationGraph q j))
    (infinityProductMap q j d)
  have hv := unitEndomorphismPullback_app_one r ((asIso φ).inv ≫ φ)
  apply hv.trans
  rw [asIso_inv, IsIso.inv_hom_id]
  change r.appTop (1 : Γ(pullback (pullback.snd (j ≫ q) q) d, ⊤)) = 1
  exact map_one r.appTop.hom

end AlgebraicGeometry.Scheme.Hom
