/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.Cylinder.H1ChartVanishing
public import Motivic.Cohomology.A1.LocalVanishing.Cylinder.EtaleRestriction
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cartier.CylinderComparison
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cartier.PunctureComparison
public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Lifting.DistinguishedSquare

/-! # Degree-one restriction Mono for the actual marked Cartier pair

The geometric producer chooses a common etale chart on the original base,
retaining the full field-valued mark. The chart localization sequence then
proves the literal original cylinder restriction monic. Only the genuine
canonical contraction-to-boundary Epi inputs remain; no puncture-Mono or
abstract refinement family is assumed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf

/-- At any complete field-valued mark on a smooth Cartier divisor, the actual
degree-one cylinder-to-puncture colimit map is monic, conditional only on the
genuine canonical boundary epimorphisms. Infinite base field is used by dense
coefficient detection, not by a replacement of the marking field. -/
theorem pointedCylinderRestriction_H1_mono_of_cartier_of_boundary_epi
    {k : Type u} [Field k] [Infinite k]
    [HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (Y : SmoothSite (Spec (.of k))) (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant)
    (hE : ∀ X : SmoothSite (Spec (.of k)), Epi (contractionToBoundary X F hF))
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)]
    (hI : IsLocallyRankOne Y.left (Scheme.Hom.idealModule i))
    {U : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
    (hcomp : Set.range i = (Set.range j.left)ᶜ)
    (K : Type u) [Field K] (b : Spec (.of K) ⟶ Y.left) (s : Spec (.of K))
    (hb : b s ∈ Set.range i) :
    Mono (colim.map (pointedCylinderRestriction (.of k) j
      (relativeFieldPoint b K (𝟙 _))
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) 1))) := by
  let P := LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1
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
  obtain ⟨hA, t, hB⟩ := SmoothSite.exists_cartier_puncture_comparison
    (.of k) j a q d i O.ι hpa hpq hcomp
  let w := SmoothSite.etalePullbackSnd j a
  let qU := SmoothSite.etalePullbackFst j a
  let : IsOpenImmersion w.left :=
    inferInstanceAs (IsOpenImmersion (pullback.snd j.left a.left))
  let : Mono (colim.map (pointedCylinderRestriction (.of k) w
      (relativeFieldPoint bE K (𝟙 _)) P)) :=
    pointedCylinderRestriction_H1_colimit_mono_of_chart
      D q F w t hB hF (hE D) (hE (SmoothSite.a1Cylinder (.of k) D))
      (relativeFieldPoint bE K (𝟙 _))
  have h := fieldPoint_cylinderRestriction_mono_of_etale
    (.of k) P j a w qU hA K bE
  let M (c : Spec (.of K) ⟶ Y.left) : Prop :=
    Mono (colim.map (pointedCylinderRestriction (.of k) j
      (relativeFieldPoint c K (𝟙 _)) P))
  change M b
  exact Eq.mp (congrArg M hbE) (show M (bE ≫ a.left) from h)

end Motivic.FiniteEtaleSite
