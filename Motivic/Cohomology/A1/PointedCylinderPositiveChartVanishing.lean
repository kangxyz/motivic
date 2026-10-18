/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PointedCylinderPositiveSupport
public import Motivic.Cohomology.A1.PointedCylinderH1ChartVanishing
public import Motivic.Cohomology.A1.ContractionBoundaryIso

/-! # The positive left localization term kills an original cylinder germ

The actual coefficient restriction is monic by the proved dense-open theorem.
The original Ext localization sequence then reduces degree `n + 2` to supported
cohomology in degree `n + 1`. Only that lower degree for the contraction is
assumed homotopy invariant. The result retains the full field-valued mark and
the original marked BASE refinement before taking the whole cylinder.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe u v w t

namespace Motivic.SheafCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- Original restriction commutes with the original Ext connecting class.
A zero restriction of the left localization term therefore kills its boundary. -/
theorem boundary_restriction_eq_zero_of_restriction_eq_zero
    {S : ShortComplex (Sheaf J AddCommGrpCat.{max v t})} (hS : S.ShortExact)
    (n : ℕ) {X Y : C} (y : H J S.X₃ n X) (f : Y ⟶ X)
    (hy : (presheaf J S.X₃ n).map f.op y = 0) :
    (presheaf J S.X₁ (n + 1)).map f.op (y.comp hS.extClass rfl) = 0 := by
  rw [restriction_apply,
    ← Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)]
  change ((presheaf J S.X₃ n).map f.op y).comp hS.extClass rfl = 0
  rw [hy, Ext.zero_comp]

end Motivic.SheafCohomology

namespace Motivic.FiniteEtaleSite

local instance chartPositiveHasExt (S : Scheme.{u}) :
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
  (hE : Epi (contractionToBoundary (SmoothSite.a1Cylinder (.of k) X) F hF))
  (K : Type u) [Field K] (c : Spec (.of K) ⟶ X.left) (n : ℕ)
  (hH : (SheafCohomology.withTransfers k (SheafWithTransfers.contraction F hF)
    (n + 1)).IsA1Invariant)

local notation "G" => Functor.obj (SheafWithTransfers.toSheaf k) F
local notation "E₁" => SmoothSite.a1Cylinder (CommRingCat.of k) E
local notation "πE" => SmoothSite.a1Projection (CommRingCat.of k) E
local notation "j₁" => SmoothSite.a1Map (CommRingCat.of k) j
local notation "Φ" => relativeFieldPoint (c ≫ d.left) K (𝟙 _)

include hj hd hF hE hH in
/-- The actual degree `n + 2` coefficient kernel is killed on a whole cylinder
after a genuine full-K marked BASE refinement. No puncture-cohomology Mono or
abstract support-vanishing family is supplied. -/
theorem exists_pointed_chart_positive_coefficient_kernel_restriction_zero
    (V : (Φ).fiber.Elements)
    (x : SheafCohomology.H.{u + 1, u + 1, u, u + 1} (nisnevichTopology (E₁).left)
      ((restrict E₁ AddCommGrpCat).obj G) (n + 2) ((baseChange (πE).left).obj V.obj))
    (hx : x.comp (Ext.mk₀ (restrictionToDirectImage G j₁)) (add_zero (n + 2)) = 0) :
    ∃ (W : (Φ).fiber.Elements) (a : W ⟶ V),
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (nisnevichTopology (E₁).left) ((restrict E₁ AddCommGrpCat).obj G) (n + 2)).map
          ((baseChange (πE).left).map a.hom).op x = 0 := by
  let J := nisnevichTopology (E₁).left
  let r := restrictionToDirectImage G j₁
  let := chartProduct_restrictionToDirectImage_mono X b F j q hj hF
  let S := ShortComplex.mk r (cokernel.π r) (cokernel.condition r)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
    (Hypercohomology.freeAbelianSheaf J ((baseChange (πE).left).obj V.obj)) hS x hx rfl
  obtain ⟨W, a, ha⟩ := exists_pointed_chartProductSupport_restriction_zero
    X b F j q hj d hd hF hE K c n hH V y
  refine ⟨W, a, ?_⟩
  have hz := SheafCohomology.boundary_restriction_eq_zero_of_restriction_eq_zero J hS
    (n + 1) y ((baseChange (πE).left).map a.hom) ha
  rwa [hy] at hz

include hj hd hF hH in
/-- The original degree `n + 2` cylinder germ dies in the coefficient kernel,
using lower-degree HI only for the unchanged contraction coefficient. The
canonical boundary epimorphism is the proved one, not a supplied input. -/
theorem pointedCylinder_positive_germ_zero_of_chart_coefficient_kernel
    (V : (Φ).fiber.Elements)
    (s : (pointedCylinderValues (.of k) Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G (n + 2))
      (pointedBase (.of k) Φ)).obj (op V))
    (hs : ((pointedCylinderOrdinaryIso (.of k) E Φ G (n + 2)).hom.app (op V) s).comp
      (Ext.mk₀ (restrictionToDirectImage G j₁)) (add_zero (n + 2)) = 0) :
    colimit.ι (pointedCylinderValues (.of k) Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G (n + 2))
      (pointedBase (.of k) Φ)) (op V) s = 0 := by
  obtain ⟨W, a, ha⟩ := exists_pointed_chart_positive_coefficient_kernel_restriction_zero
    X b F j q hj d hd hF
    (contractionToBoundary_epi (SmoothSite.a1Cylinder (.of k) X) F hF) K c n hH V
      ((pointedCylinderOrdinaryIso (.of k) E Φ G (n + 2)).hom.app (op V) s) hs
  exact pointedCylinder_germ_eq_zero_of_ordinary_base_refinement
    (.of k) E Φ G (n + 2) a s ha

end Motivic.FiniteEtaleSite
