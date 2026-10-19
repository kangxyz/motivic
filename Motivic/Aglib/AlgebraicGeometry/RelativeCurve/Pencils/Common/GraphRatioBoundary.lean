/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.PrescribedGraphRatio
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.BoundaryCoordinate

/-! # The actual disjoint-source graph ratio on the whole boundary

Only the original common source over the disjoint parameter is used. The graph
pole becomes a unit here because its coordinate is the pullback of the original
fixed boundary automorphism. This does not invert the generic marked graph pole.


Intended upstream module: `Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.GraphRatioBoundary`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.FunctionalGraphRatioBoundary`.
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

/-- The ratio of the SAME prescribed numerator and graph-twisted denominator
is the inverse fixed correction coordinate on the full common boundary.
The denominator-unit proof is derived here, not imposed on the generic parameter. -/
theorem commonGraphRatio_boundary_inverse
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
      (coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)) aS)] :
    let f := commonBoundaryToLambda π j α s d ≫
      coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)
    let cS := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) T
      (Hom.idealInclusion (Hom.compactificationGraph π j)) bS
    ∃ hc : IsIso (pullbackSectionMap f cS),
      ∃ hθ : IsIso (Hom.unitEndomorphismPullback
        (commonBoundaryToPsi q π j p hq a α β h z s hs d)
        (fixedProductBoundaryFrame q π a z e ha d).hom),
      let := hc
      letI := hθ
      pullbackSectionMap f aS ≫ inv (pullbackSectionMap f cS) =
        inv (Hom.unitEndomorphismPullback
          (commonBoundaryToPsi q π j p hq a α β h z s hs d)
          (fixedProductBoundaryFrame q π a z e ha d).hom) := by
  let vA := commonBoundaryToLambda π j α s d
  let zA := coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)
  let E := Hom.relativeFullBoundaryFrame q π j p hq z s hs H e d hd
  let I := Hom.relativeCompactificationGraphLine π j
  let φ := Hom.idealInclusion (Hom.compactificationGraph π j)
  let E' := compositeBoundaryFrame vA zA (dualLineBundle _ I).val E
  let θ := Hom.unitEndomorphismPullback
    (commonBoundaryToPsi q π j p hq a α β h z s hs d)
    (fixedProductBoundaryFrame q π a z e ha d).hom
  have hδ : pullbackSectionMap (vA ≫ zA) (canonicalDualHom _ I.val φ) ≫ E'.hom = θ := by
    exact (compositeBoundaryFrame_coordinate vA zA (dualLineBundle _ I).val E
      (canonicalDualHom _ I.val φ)).trans
        (commonBoundary_coordinate_eq q π a z e ha d j p hq α β h s hs H hd)
  have hpair := prescribed_pair_pullback vA zA T.val (dualLineBundle _ I).val E aS bS hA
  have : IsIso (pullbackSectionMap (vA ≫ zA) aS) := by
    rw [← pullbackSectionMap_comp]
    have : IsIso (pullbackSectionMap vA (pullbackSectionMap zA aS)) := by
      change IsIso ((pullbackUnitIso vA).inv ≫
        (Modules.pullback vA).map (pullbackSectionMap zA aS))
      infer_instance
    infer_instance
  have : IsIso θ := by
    dsimp only [θ, Hom.unitEndomorphismPullback]
    infer_instance
  have : IsIso (pullbackSectionMap (vA ≫ zA) (canonicalDualHom _ I.val φ) ≫ E'.hom) := by
    rw [hδ]
    infer_instance
  have hc := prescribed_pair_twistedIdealSection_isIso (vA ≫ zA) I T φ aS bS E' hpair
  let := hc
  refine ⟨hc, inferInstance, ?_⟩
  change pullbackSectionMap (vA ≫ zA) aS ≫
    inv (pullbackSectionMap (vA ≫ zA) (twistedIdealSection _ I T φ bS)) = inv θ
  apply (cancel_mono (pullbackSectionMap (vA ≫ zA) (twistedIdealSection _ I T φ bS))).mp
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hcθ : pullbackSectionMap (vA ≫ zA) (twistedIdealSection _ I T φ bS) =
      θ ≫ pullbackSectionMap (vA ≫ zA) aS :=
    (prescribed_pair_twistedIdealSection_eq_coordinate (vA ≫ zA) I T φ aS bS E' hpair).trans
      (congrArg (fun ξ => ξ ≫ pullbackSectionMap (vA ≫ zA) aS) hδ)
  rw [hcθ, IsIso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
