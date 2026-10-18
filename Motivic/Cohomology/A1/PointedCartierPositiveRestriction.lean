/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PointedCylinderPositiveRestriction
public import Motivic.Cohomology.A1.PointedEtaleCylinderRestriction
public import Motivic.AlgebraicGeometry.SmoothSiteCartierCylinderComparison
public import Motivic.AlgebraicGeometry.SmoothSiteCartierPunctureComparison
public import Motivic.Aglib.AlgebraicGeometry.NisnevichDistinguishedSquare

/-! # Actual higher-degree Cartier puncture restriction

The full field-valued mark is transported through the original etale chart.
Positive higher open images use only strictly lower degrees for the original
coefficient. The support term uses the lower contraction degree. No current-
degree homotopy invariance, supplied puncture Mono, or boundary Epi is assumed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace Motivic.FiniteEtaleSite

/-- At any unchanged full-K mark on an actual smooth Cartier divisor, the
original degree `n + 2` cylinder-to-puncture colimit map is monic under the
strictly lower coefficient and contraction homotopy-invariance inputs. -/
theorem pointedCylinderRestriction_positive_mono_of_cartier
    {k : Type u} [Field k] [Infinite k]
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
      D q F w t hB d hd hF K c n hLow hContract
  have h := fieldPoint_cylinderRestriction_mono_of_etale
    (.of k) P j a w qU hA K bE
  let M (c : Spec (.of K) ⟶ Y.left) : Prop :=
    Mono (colim.map (pointedCylinderRestriction (.of k) j
      (relativeFieldPoint c K (𝟙 _)) P))
  change M b
  exact Eq.mp (congrArg M hbE) (show M (bE ≫ a.left) from h)

end Motivic.FiniteEtaleSite
