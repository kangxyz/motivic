/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairGraphCoordinate
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.GraphChartFactors
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.MarkedFiber

/-! # The actual marked norm in the original section-induced ideal frame

The original numerator and pole determine the frame. Both marked and residual
factors are constructed from the actual finite chart and thickened boundary.
The graph coefficient can vanish on the marked scheme.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairGraphMarkedNorm`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Norm.RetainedSectionPairGraph`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S X Y Z C D : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (π : C ⟶ S) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ π = p ≫ q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))
  (T : LineBundle (pullback (j ≫ π) π))
  (aS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))).val)
  (bS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ T.val)
  (hA : pullbackSectionMap (Hom.fullBoundaryProductMap π j d s) aS ≫
      pullbackTensorMap (Hom.fullBoundaryProductMap π j d s) T.val
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)).val =
    tensorUnitSection (pullbackSectionMap (Hom.fullBoundaryProductMap π j d s) bS)
      (Hom.relativeFullBoundaryFrame q π j p hq z s hs H e d hd).inv)


variable {R Q : Type u} [CommRing R] [CommRing Q] {W V K : Scheme.{u}}
  (f : C ⟶ K) [IsFinite f] (zK : Z ⟶ K) (hsK : (s ≫ j) ≫ f = zK)
  (n : W ⟶ Spec (.of R)) [IsFinite n] (φ : R →+* Q)
  (k : V ⟶ W) [IsOpenImmersion k] (σ : Spec (.of Q) ⟶ V)
  (hn : (σ ≫ k) ≫ n = Spec.map (CommRingCat.ofHom φ))
  (HN : IsPullback σ (𝟙 _) (k ≫ n) (Spec.map (CommRingCat.ofHom φ)))
  (u : W ⟶ C) (t : Spec (.of R) ⟶ K) (Hf : IsPullback u n f t)
  (a : Spec (.of Q) ⟶ Z)
  (hz : Spec.map (CommRingCat.ofHom φ) ≫ t = a ≫ zK)
  (hj : a ≫ (s ≫ j) = (σ ≫ k) ≫ u)
  (w : W ⟶ pullback (j ≫ π) π)
  (hw : w ≫ pullback.snd (j ≫ π) π = u)
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _ T bS) w)]
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _
    (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))) aS) w)]
  (bE : (Scheme.residualMarkedFiberOpen f j zK s hsK).toScheme ⟶ D)
  (hbE : bE ≫ d = Scheme.residualMarkedFiberMap f j zK s hsK)

include hA hn HN Hf hz hbE in
/-- The norm of the deterministic graph coefficient has the same supplied marked
coordinate. Freeness concerns only the actual total finite-chart algebra. -/
theorem sectionPairGraphCoefficient_norm_marked_value :
    let c : Γ(W, ⊤) := Modules.Hom.app (sectionPairGraphCoefficient π j T aS bS w) ⊤ (1 : Γ(W, ⊤))
    let α := Scheme.graphChartMarkedFactor π j s k σ u a hj w hw
    let m := Modules.Hom.app (Hom.unitEndomorphismPullback
      (α ≫ (Hom.relativeBoundaryProductIso q π j p hq z s hs).hom ≫
        Hom.boundaryProductMap q p z)
      (e.hom ≫ Hom.idealInclusion (Hom.boundaryGraphTarget q z))) ⊤ (1 : Γ(Spec (.of Q), ⊤))
    let : Algebra R Γ(W, ⊤) := (FiniteSchemeNormBaseChange.scalarMap n).toAlgebra
    ∀ [Module.Free R Γ(W, ⊤)], φ (Algebra.norm R c) = (Scheme.ΓSpecIso (.of Q)).hom m := by
  dsimp only
  let c : Γ(W, ⊤) := Modules.Hom.app (sectionPairGraphCoefficient π j T aS bS w) ⊤ (1 : Γ(W, ⊤))
  let α := Scheme.graphChartMarkedFactor π j s k σ u a hj w hw
  let r := Scheme.graphChartResidualFactor π j s f zK hsK n k σ
    (Spec.map (CommRingCat.ofHom φ)) hn u t Hf a hz hj w hw d bE hbE
  apply FiniteSchemeNormBaseChange.norm_eq_marked_value n φ k σ hn HN c
  · have hm := sectionPairGraphCoefficient_marked_scalar q π j p hq z s hs H e d hd
      T aS bS hA w (σ ≫ k) α
      (Scheme.graphChartMarkedFactor_ambient π j s k σ u a hj w hw).symm
    simpa only [Iso.hom_inv_id_apply] using hm
  · have hr := sectionPairGraphCoefficient_infinity_scalar q π j p hq z s hs H e d hd
      T aS bS hA w (Scheme.residualMarkedFiberMap n k (Spec.map (CommRingCat.ofHom φ)) σ hn)
      r (Scheme.graphChartResidualFactor_ambient π j s f zK hsK n k σ
        (Spec.map (CommRingCat.ofHom φ)) hn u t Hf a hz hj w hw d bE hbE).symm
    exact hr

end AlgebraicGeometry.Scheme.RelativeCurvePencil
