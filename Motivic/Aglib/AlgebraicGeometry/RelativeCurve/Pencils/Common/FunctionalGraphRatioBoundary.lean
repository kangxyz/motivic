/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.GraphRatioBoundary
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.FunctionalRatio

/-! # The actual disjoint-source graph ratio on the whole boundary

Only the original common source over the disjoint parameter is used. The graph
pole becomes a unit here because its coordinate is the pullback of the original
fixed boundary automorphism. This does not invert the generic marked graph pole.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.FunctionalGraphRatioBoundary`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S X Y A B Z C D : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : C ⟶ S) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ π = p ≫ q)
  (a : A ⟶ X) [Flat a] (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  (hd : Disjoint (Set.range j) (Set.range d))

/-- The actual local functional ratio of the original target pair has the inverse
fixed correction coordinate on each genuine common-boundary chart. The coordinate
unit is derived from the original disjoint parameter, never assumed generically. -/
theorem commonFunctionalGraphRatio_boundary_inverse
    (T : LineBundle (pullback (j ≫ π) π))
    (aS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
      (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))).val)
    (bS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ T.val)
    (hA : let zA := coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)
      pullbackSectionMap zA aS ≫ pullbackTensorMap zA T.val
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)).val =
      tensorUnitSection (pullbackSectionMap zA bS)
        (Hom.relativeFullBoundaryFrame q π j p hq z s hs H e d hd).inv)
    [IsIso (pullbackSectionMap
      (coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)) aS)]
    {W Q : Scheme.{u}} (w : W ⟶ pullback (j ≫ π) π)
    (r : Q ⟶ W) (v : Q ⟶ commonBoundary π j α s d)
    (hr : r ≫ w = v ≫ commonBoundaryToLambda π j α s d ≫
      coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s))
    [IsIso (pullbackUnitMap w (sectionDualFunctional _
      (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)))
      (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) T
        (Hom.idealInclusion (Hom.compactificationGraph π j)) bS)))] :
    let L := tensorLineBundle _ T
      (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))
    let cS := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) T
      (Hom.idealInclusion (Hom.compactificationGraph π j)) bS
    let θ := Hom.unitEndomorphismPullback
      (commonBoundaryToPsi q π j p hq a α β h z s hs d)
      (fixedProductBoundaryFrame q π a z e ha d).hom
    ∃ hθ : IsIso θ, letI := hθ
      Hom.unitEndomorphismPullback r
        (inv (pullbackUnitMap w (sectionDualFunctional _ L cS)) ≫
          pullbackUnitMap w (sectionDualFunctional _ L aS)) =
        Hom.unitEndomorphismPullback v (inv θ) := by
  let f := commonBoundaryToLambda π j α s d ≫
    coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)
  let L := tensorLineBundle _ T
    (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))
  let cS := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) T
    (Hom.idealInclusion (Hom.compactificationGraph π j)) bS
  let θ := Hom.unitEndomorphismPullback
    (commonBoundaryToPsi q π j p hq a α β h z s hs d)
    (fixedProductBoundaryFrame q π a z e ha d).hom
  obtain ⟨hc, hθ, he⟩ := commonGraphRatio_boundary_inverse
    q π j p hq a α β h z s hs H e ha d hd T aS bS hA
  let := hc
  let := hθ
  refine ⟨hθ, ?_⟩
  have hsec : pullbackSectionMap f aS = inv θ ≫ pullbackSectionMap f cS := by
    calc
      pullbackSectionMap f aS =
          (pullbackSectionMap f aS ≫ inv (pullbackSectionMap f cS)) ≫
            pullbackSectionMap f cS := by simp only [Category.assoc, IsIso.inv_hom_id,
              Category.comp_id]
      _ = inv θ ≫ pullbackSectionMap f cS :=
        congrArg (fun ξ => ξ ≫ pullbackSectionMap f cS) he
  apply functionalQuotient_boundary_of_sectionEquation w r L aS cS
  have hh := scalar_pair_pullback v f aS cS (inv θ) hsec
  have hr' : r ≫ w = v ≫ f := by simpa only [f, Category.assoc] using hr
  rw [← hr'] at hh
  exact hh

end AlgebraicGeometry.Scheme.RelativeCurvePencil
