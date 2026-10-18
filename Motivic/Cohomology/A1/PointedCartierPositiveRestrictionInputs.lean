/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PointedCartierH1RestrictionInputs
public import Motivic.Cohomology.A1.PointedCylinderPositiveSupport
public import Motivic.Cohomology.A1.PointedCylinderPositiveChartVanishing
public import Motivic.Cohomology.A1.ContractionChartHigherImageInputs

/-! # Higher full-marked Cartier restriction from original coefficient inputs

The local-zero and canonical Epi families are explicit inputs, not finite-field
producers. The only cohomological hypotheses are strictly lower original
degrees and degree N-1 of the actual contraction. Existing supported-cohomology
and marked BASE comparison machinery is reused without changing its objects.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace Motivic.FiniteEtaleSite.CoefficientInputs

local instance chartPositiveHasExt (S : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

variable {k : Type u} [Field k]
  (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
  (hEpi : OriginalPresheaf.CanonicalBoundaryEpi k)
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

include hD hj hd hF hE hH in
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
  let := chartProduct_restrictionToDirectImage_mono hD X b F j q hj hF
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

include hD hEpi hj hd hF hH in
/-- The original degree `n + 2` cylinder germ dies in the coefficient kernel,
using lower-degree HI only for the unchanged contraction coefficient. The
canonical boundary epimorphism comes from the explicit original Epi input. -/
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
    hD X b F j q hj d hd hF
    (contractionToBoundary_epi_of_canonicalBoundaryEpi hEpi
      (SmoothSite.a1Cylinder (.of k) X) F hF) K c n hH V
      ((pointedCylinderOrdinaryIso (.of k) E Φ G (n + 2)).hom.app (op V) s) hs
  exact pointedCylinder_germ_eq_zero_of_ordinary_base_refinement
    (.of k) E Φ G (n + 2) a s ha

end Motivic.FiniteEtaleSite.CoefficientInputs

namespace Motivic.FiniteEtaleSite.CoefficientInputs

local instance positiveRestrictionHasExt (S : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

variable {k : Type u} [Field k]
  (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
  (hEpi : OriginalPresheaf.CanonicalBoundaryEpi k)
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

include hD hEpi hj hd hF hLow hContract in
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
          hD hEpi X b F j q hj d hd r (hLow (r + 1) (Nat.succ_pos r) hmn))
    rw [map_zero]
    have he := ordinaryEdgeMap_restrictionToDirectImage j₁ G (n + 2) V₁ t
    change ordinaryEdgeMap (j₁).left V₁ ((restrict U₁ AddCommGrpCat).obj G) (n + 2)
        (x.comp (Ext.mk₀ (restrictionToDirectImage G j₁)) (add_zero (n + 2))) =
      cohomologyRestrictionEquiv U₁ G (n + 2) ((baseChange (j₁).left).obj V₁)
        (P.map ((restrictionProjection j₁).app V₁).op t) at he
    rw [ht, map_zero] at he
    exact he
  apply pointedCylinder_positive_germ_zero_of_chart_coefficient_kernel
    hD hEpi X b F j q hj d hd hF K c n hContract V s
  exact hx

include hD hEpi hj hd hF hLow hContract in
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
    hD hEpi X b F j q hj d hd hF K c n hLow hContract W.unop (D.map a s) hlocal
  have hw := ConcreteCategory.congr_hom (colimit.w D a) s
  exact hw.symm.trans hzero

end Motivic.FiniteEtaleSite.CoefficientInputs

namespace Motivic.FiniteEtaleSite.CoefficientInputs

/-- At any unchanged full-K mark on an actual smooth Cartier divisor, the
original degree `n + 2` cylinder-to-puncture colimit map is monic under the
strictly lower coefficient and contraction homotopy-invariance inputs. -/
theorem pointedCylinderRestriction_positive_mono_of_cartier
    {k : Type u} [Field k]
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    (hEpi : OriginalPresheaf.CanonicalBoundaryEpi k)
    [HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (Y : SmoothSite (Spec (.of k))) (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant)
    (n : ℕ)
    (hLow : ∀ m : ℕ, 0 < m → m < n + 2 →
      (SheafCohomology.withTransfers k F m).IsA1Invariant)
    (hContract : (SheafCohomology.withTransfers k
      (SheafWithTransfers.contraction F hF) (n + 1)).IsA1Invariant)
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)]
    (hI : IsLocallyRankOne Y.left (Scheme.Hom.idealModule i))
    {U : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
    (hcomp : Set.range i = (Set.range j.left)ᶜ)
    (K : Type u) [Field K] (b : Spec (.of K) ⟶ Y.left) (s : Spec (.of K))
    (hb : b s ∈ Set.range i) :
    Mono (colim.map (pointedCylinderRestriction (.of k) j
      (relativeFieldPoint b K (𝟙 _))
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) (n + 2)))) := by
  let P := SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) (n + 2)
  have hs : (IsLocalRing.closedPoint K : PrimeSpectrum K) = s := Subsingleton.elim _ _
  obtain ⟨cZ, hcZ⟩ := Scheme.exists_field_lift_of_mem_range i b
    (by simpa only [hs] using hb)
  obtain ⟨O, hO, E, a, q, d, ha, hq, hpa, hpq⟩ :=
    SmoothSite.exists_cartier_cylinder_comparison Y i hI (cZ s)
  let D := SmoothSite.closedOpenSite (Y := Y) i O
  let c := openFieldPointLift K cZ s O hO
  let bE := c ≫ d.left
  have hc : c ≫ O.ι = cZ := openFieldPointLift_ι K cZ s O hO
  have hbE : bE ≫ a.left = b := by
    change (c ≫ d.left) ≫ a.left = b
    rw [Category.assoc, hpa.w, ← Category.assoc, hc]
    exact hcZ
  let : Etale a.left := ha
  let : Etale q.left := hq
  have hd : IsPullback d (𝟙 D) q (SmoothSite.a1Section (.of k) D 0) := by
    apply IsPullback.of_map_of_faithful (SmoothSite.forgetScheme (Spec (.of k)))
    exact hpq
  obtain ⟨hA, t, hB⟩ := SmoothSite.exists_cartier_puncture_comparison
    (.of k) j a q d i O.ι hpa hpq hcomp
  let w := SmoothSite.etalePullbackSnd j a
  let qU := SmoothSite.etalePullbackFst j a
  let : IsOpenImmersion w.left :=
    inferInstanceAs (IsOpenImmersion (pullback.snd j.left a.left))
  let : Mono (colim.map (pointedCylinderRestriction (.of k) w
      (relativeFieldPoint bE K (𝟙 _)) P)) :=
    pointedCylinderRestriction_positive_colimit_mono_of_chart
      hD hEpi D q F w t hB d hd hF K c n hLow hContract
  have h := fieldPoint_cylinderRestriction_mono_of_etale
    (.of k) P j a w qU hA K bE
  let M (c : Spec (.of K) ⟶ Y.left) : Prop :=
    Mono (colim.map (pointedCylinderRestriction (.of k) j
      (relativeFieldPoint c K (𝟙 _)) P))
  change M b
  exact Eq.mp (congrArg M hbE) (show M (bE ≫ a.left) from h)

end Motivic.FiniteEtaleSite.CoefficientInputs
