/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PointedCylinderPositiveChartVanishing
public import Motivic.Cohomology.A1.ContractionChartHigherImageVanishing

/-! # Actual positive puncture restriction on a full-marked cylinder chart

Only positive degrees strictly below the target are used for the original
coefficient's higher-open-image window. The left localization term uses the
specified lower degree of the contraction. The original puncture map, ordinary
edge, coefficient restriction, and marked BASE colimit are unchanged.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite

local instance positiveRestrictionHasExt (S : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

variable {k : Type u} [Field k] [Infinite k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (X : SmoothSite (Spec (.of k))) {E U : SmoothSite (Spec (.of k))}
  (b : E ⟶ SmoothSite.a1Cylinder (.of k) X) [Etale b.left]
  (F : SheafWithTransfers.{u + 1} k) (j : U ⟶ E)
  (q : U ⟶ SmoothSite.torusCylinder (.of k) X)
  (hj : IsPullback q j (SmoothSite.contractionOpen (.of k) X) b)
  (d : X ⟶ E) (hd : IsPullback d (𝟙 X) b (SmoothSite.a1Section (.of k) X 0))
  (hF : F.obj.IsA1Invariant)
  (K : Type u) [Field K] (c : Spec (.of K) ⟶ X.left) (n : ℕ)
  (hLow : ∀ m : ℕ, 0 < m → m < n + 2 →
    (SheafCohomology.withTransfers k F m).IsA1Invariant)
  (hContract : (SheafCohomology.withTransfers k (SheafWithTransfers.contraction F hF)
    (n + 1)).IsA1Invariant)

local notation "G" => Functor.obj (SheafWithTransfers.toSheaf k) F
local notation "E₁" => SmoothSite.a1Cylinder (CommRingCat.of k) E
local notation "U₁" => SmoothSite.a1Cylinder (CommRingCat.of k) U
local notation "πE" => SmoothSite.a1Projection (CommRingCat.of k) E
local notation "j₁" => SmoothSite.a1Map (CommRingCat.of k) j
local notation "Φ" => relativeFieldPoint (c ≫ d.left) K (𝟙 _)

include hj hd hF hLow hContract in
/-- The actual lower higher-image window makes the original open edge injective.
The literal puncture triangle then supplies the genuine coefficient-kernel
equation, which is killed by a full-K marked BASE refinement. -/
theorem pointedCylinder_positive_germ_zero_of_chart_puncture_restriction_zero
    (V : (Φ).fiber.Elements)
    (s : (pointedCylinderValues (.of k) Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G (n + 2))
      (pointedBase (.of k) Φ)).obj (op V))
    (hs : (pointedCylinderRestriction (.of k) j Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G (n + 2))).app (op V) s = 0) :
    colimit.ι (pointedCylinderValues (.of k) Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G (n + 2))
      (pointedBase (.of k) Φ)) (op V) s = 0 := by
  let P := SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) G (n + 2)
  let V₁ := (baseChange (πE).left).obj V.obj
  let t := P.map (a1BaseChangeIso (.of k) E V.obj).hom.op s
  have ht : P.map ((restrictionProjection j₁).app V₁).op t = 0 := by
    change P.map ((restrictionProjection j₁).app V₁).op
      (P.map (a1BaseChangeIso (.of k) E V.obj).hom.op s) = 0
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      a1PunctureProjectionBaseChangeIso_restriction]
    change P.map (SmoothSite.a1Map (.of k) ((restrictionProjection j).app V.obj)).op s = 0
      at hs
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    erw [hs]
    simp only [map_zero]
  let x := cohomologyRestrictionEquiv E₁ G (n + 2) V₁ t
  have hx : x.comp (Ext.mk₀ (restrictionToDirectImage G j₁)) (add_zero (n + 2)) = 0 := by
    apply ordinaryEdgeMap_injective_of_rightDerived_window (j₁).left V₁
      ((restrict U₁ AddCommGrpCat).obj G) (n + 2) (by
        intro m hm hmn
        obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
        exact chartProduct_higherDirectImage_isZero_succ
          X b F j q hj d hd r (hLow (r + 1) (Nat.succ_pos r) hmn))
    rw [map_zero]
    have he := ordinaryEdgeMap_restrictionToDirectImage j₁ G (n + 2) V₁ t
    change ordinaryEdgeMap (j₁).left V₁ ((restrict U₁ AddCommGrpCat).obj G) (n + 2)
        (x.comp (Ext.mk₀ (restrictionToDirectImage G j₁)) (add_zero (n + 2))) =
      cohomologyRestrictionEquiv U₁ G (n + 2) ((baseChange (j₁).left).obj V₁)
        (P.map ((restrictionProjection j₁).app V₁).op t) at he
    rw [ht, map_zero] at he
    exact he
  apply pointedCylinder_positive_germ_zero_of_chart_coefficient_kernel
    X b F j q hj d hd hF K c n hContract V s
  exact hx

include hj hd hF hLow hContract in
/-- The original positive-degree cylinder-to-puncture map is monic at the
unchanged full-K chart mark. All higher-image and support vanishings are derived
from the displayed lower-degree homotopy-invariance inputs. -/
theorem pointedCylinderRestriction_positive_colimit_mono_of_chart :
    Mono (colim.map (pointedCylinderRestriction (.of k) j Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G (n + 2)))) := by
  let P := SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) G (n + 2)
  let D := pointedCylinderValues (.of k) Φ P (pointedBase (.of k) Φ)
  let T := pointedCylinderValues (.of k) Φ P (pointedPuncture (.of k) j Φ)
  let r := pointedCylinderRestriction (.of k) j Φ P
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨V, v, s, rfl⟩ := (Φ).toPresheafFiber_jointly_surjective
    (P := (toSmoothSite E ⋙ SmoothSite.parameterProduct (SmoothSite.affineLine (.of k))).op ⋙ P) z
  let N : (Φ).fiber.Elements := Functor.elementsMk _ V v
  have he : colimit.ι T (op N) (r.app (op N) s) = colimit.ι T (op N) 0 := by
    rw [map_zero]
    have h := ConcreteCategory.congr_hom (colimit.ι_map r (op N)) s
    exact h.symm.trans hz
  obtain ⟨W, a, ha⟩ := ((colimit.isColimit T).eq_iff' (r.app (op N) s) 0).mp he
  have hlocal : r.app W (D.map a s) = 0 := by
    rw [NatTrans.naturality_apply]
    simpa only [map_zero] using ha
  have hzero := pointedCylinder_positive_germ_zero_of_chart_puncture_restriction_zero
    X b F j q hj d hd hF K c n hLow hContract W.unop (D.map a s) hlocal
  have hw := ConcreteCategory.congr_hom (colimit.w D a) s
  exact hw.symm.trans hzero

end Motivic.FiniteEtaleSite
