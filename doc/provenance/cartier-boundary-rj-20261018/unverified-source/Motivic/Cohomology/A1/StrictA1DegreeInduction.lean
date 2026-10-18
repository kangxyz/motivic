/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PositiveRankCartierReduction
public import Motivic.Cohomology.A1.RankZeroCylinderVanishing
public import Motivic.Cohomology.A1.FiniteLerayHI
public import Motivic.Cohomology.A1.DegreeZero
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleMarkedPointDetection
public import Motivic.Aglib.AlgebraicGeometry.SmoothStalkFiniteRank

/-! # Original strict A1: degree and finite local-rank induction

The sole mathematical theorem-family input below is the original cohomological
puncture-restriction monomorphism for smooth Cartier complements. It is not the
contraction-to-boundary monomorphism. The family is an explicit argument, not an
instance or an assertion that its missing producer has been proved.

The outer induction quantifies over all HI Nisnevich transfer sheaves: a future
producer of the puncture mono must apply lower degrees also to contractions.
The inner induction uses finite dimensions of actual smooth stalks, the proved
rank-zero result, and the actual local Cartier reduction. Marked test-object
fibers, not only residue points of the base, detect the resulting higher image.
Finite Leray then gives the literal original projection in ordinary cohomology.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace Motivic.FiniteEtaleSite

variable {k : Type u} [Field k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The still-independent original restriction mono, on the unchanged marked
neighborhood colimit and the actual complement of a smooth Cartier divisor. -/
def SmoothCartierPunctureRestrictionMono (F : SheafWithTransfers.{u + 1} k)
    (N : ℕ) : Prop :=
  ∀ (Y : SmoothSite (Spec (.of k))) (K : Type u) [Field K]
    (b : Spec (.of K) ⟶ Y.left) (p : Spec (.of K))
    (Z : Scheme.{u}) (i : Z ⟶ Y.left),
    IsClosedImmersion i → IsLocallyRankOne Y.left (Scheme.Hom.idealModule i) →
    Smooth (i ≫ Y.hom) → b p ∈ Set.range i →
    ∀ W : Y.left.Opens, Set.range i = (W : Set Y.left)ᶜ →
      Mono (colim.map (pointedCylinderRestriction (.of k)
        (SmoothSite.openInclusion Y W) (relativeFieldPoint b K (𝟙 _))
        (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k)))
            ((SheafWithTransfers.toSheaf k).obj F) N)))

variable [PerfectField k]

/-- Local Cartier reduction with its exact missing mono supplied explicitly. -/
theorem pointedCylinderColimit_isZero_of_positive_rank_and_puncture_mono
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) (n d : ℕ)
    (hLow : ∀ q : ℕ, 0 < q → q < n + 1 →
      (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (hIH : LowerRankCylinderGermsZero F (n + 1) d)
    (hMono : SmoothCartierPunctureRestrictionMono F (n + 1))
    (X : SmoothSite (Spec (.of k))) (K : Type u) [Field K]
    (b : Spec (.of K) ⟶ X.left) (p : Spec (.of K))
    (hd : ringKrullDim (X.left.presheaf.stalk (b p)) = d) (hpos : 0 < d) :
    IsZero (colimit (pointedCylinderValues (.of k) (relativeFieldPoint b K (𝟙 _))
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) (n + 1))
      (pointedBase (.of k) (relativeFieldPoint b K (𝟙 _))))) := by
  obtain ⟨O, hO, _hAffine, Z, i, hi, hI, hs, hz, W, hW, hkill⟩ :=
    exists_positive_rank_cartier_restriction_reduction X K b p F hF n d hd hpos hLow hIH
  apply hkill
  apply hMono ((toSmoothSite X).obj (openObject O)) K
    (openFieldPointLift K b p O hO) p Z i hi hI hs
  · obtain ⟨z, hz⟩ := hz
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact hz.trans (congrArg (fun f : Spec (.of K) ⟶ X.left => f p)
      (openFieldPointLift_ι K b p O hO)).symm
  · exact hW

/-- Strong induction on the finite local rank kills every original residue
cylinder germ, conditional only on lower degrees and the original puncture mono. -/
theorem residueCylinderColimit_isZero_of_puncture_mono
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) (n : ℕ)
    (hLow : ∀ q : ℕ, 0 < q → q < n + 1 →
      (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (hMono : SmoothCartierPunctureRestrictionMono F (n + 1))
    (X : SmoothSite (Spec (.of k))) (x : X.left) :
    IsZero (colimit (pointedCylinderValues (.of k) (X := X) (residuePoint X.left x)
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) (n + 1))
      (pointedBase (.of k) (X := X) (residuePoint X.left x)))) := by
  suffices hall : ∀ d : ℕ, ∀ (Y : SmoothSite (Spec (.of k))) (y : Y.left),
      ringKrullDim (Y.left.presheaf.stalk y) = d →
      IsZero (colimit (pointedCylinderValues (.of k) (X := Y) (residuePoint Y.left y)
        (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k)))
            ((SheafWithTransfers.toSheaf k).obj F) (n + 1))
        (pointedBase (.of k) (X := Y) (residuePoint Y.left y)))) by
    obtain ⟨d, hd⟩ := Scheme.exists_nat_ringKrullDim_stalk_of_smooth X.hom x
    exact hall d X x hd
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro Y y hd
    by_cases hzero : d = 0
    · exact residueCylinderColimit_isZero_of_rank_zero F hF n Y y (hd.trans (by simp [hzero]))
    have hIH : LowerRankCylinderGermsZero F (n + 1) d := by
      intro V z hz
      obtain ⟨e, he⟩ := Scheme.exists_nat_ringKrullDim_stalk_of_smooth V.hom z
      have hed : e < d := by
        rw [he] at hz
        exact_mod_cast hz
      exact ih e hed V z he
    apply pointedCylinderColimit_isZero_of_positive_rank_and_puncture_mono F hF n d
      hLow hIH hMono Y (Y.left.residueField y) (Y.left.fromSpecResidueField y)
      (IsLocalRing.closedPoint (Y.left.residueField y))
    · exact (congrArg (fun z : Y.left => ringKrullDim (Y.left.presheaf.stalk z))
        (Y.left.fromSpecResidueField_apply y
          (IsLocalRing.closedPoint (Y.left.residueField y)))).trans hd
    · exact Nat.pos_of_ne_zero hzero

local instance (Y : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

/-- Marked fibers of every actual test object detect the original higher image. -/
theorem projectionHigherImage_isZero_of_puncture_mono
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) (n : ℕ)
    (hLow : ∀ q : ℕ, 0 < q → q < n + 1 →
      (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (hMono : SmoothCartierPunctureRestrictionMono F (n + 1))
    (X : SmoothSite (Spec (.of k))) :
    IsZero (((directImage (SmoothSite.a1Projection (.of k) X).left).rightDerived (n + 1)).obj
      ((restrict (SmoothSite.a1Cylinder (.of k) X) AddCommGrpCat.{u + 1}).obj
        ((SheafWithTransfers.toSheaf k).obj F))) := by
  apply isZero_of_all_marked_residue_fibers
  intro V z
  exact markedProjectionFiber_isZero_of_cylinderColimit (.of k) X V z
    ((SheafWithTransfers.toSheaf k).obj F) (n + 1)
    (residueCylinderColimit_isZero_of_puncture_mono F hF n hLow hMono
      ((toSmoothSite X).obj V) z)

end Motivic.FiniteEtaleSite

namespace Motivic.SheafWithTransfers
open FiniteEtaleSite
variable {k : Type u} [Field k] [hkInfinite : Infinite k] [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local instance (Y : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

include hkInfinite in
/-- Conditional infinite-perfect-field assembly. The explicit theorem-family
argument is precisely the unresolved cohomological puncture mono producer.
Its lower-degree premise ranges over all HI coefficients, including contractions;
it never assumes current-degree HI, purity, or derived continuity. -/
theorem isStrictA1Invariant_of_smoothCartierPunctureRestrictionMono
    (hMono : ∀ n : ℕ,
      (∀ (G : SheafWithTransfers.{u + 1} k), G.obj.IsA1Invariant →
        ∀ q : ℕ, 0 < q → q < n + 1 →
          (SheafCohomology.withTransfers k G q).IsA1Invariant) →
      ∀ (F : SheafWithTransfers.{u + 1} k), F.obj.IsA1Invariant →
        SmoothCartierPunctureRestrictionMono F (n + 1))
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) :
    F.IsStrictA1Invariant := by
  suffices hall : ∀ N : ℕ, ∀ (G : SheafWithTransfers.{u + 1} k), G.obj.IsA1Invariant →
      A1.IsInvariant (.of k)
        (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj G) N) by
    exact fun N => hall N F hF
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro G hG
    cases N with
    | zero => exact degreeZero_isInvariant G hG
    | succ n =>
      intro X
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      apply a1_projection_bijective_of_rightDerived_window X G hG (n + 1)
      intro q hq hqN
      cases q with
      | zero => exact (Nat.lt_irrefl 0 hq).elim
      | succ m =>
        have hLow : ∀ (H : SheafWithTransfers.{u + 1} k), H.obj.IsA1Invariant →
            ∀ r : ℕ, 0 < r → r < m + 1 →
              (SheafCohomology.withTransfers k H r).IsA1Invariant := by
          intro H hH r _hr hrm Y
          exact (NatIso.isIso_map_iff (SheafCohomology.withTransfersGraphIso k H r)
            (SmoothSite.a1Projection (.of k) Y).op).mpr
              (ih r (Nat.lt_of_lt_of_le hrm hqN) H hH Y)
        exact projectionHigherImage_isZero_of_puncture_mono G hG m (hLow G hG)
          (hMono m hLow G hG) X

end Motivic.SheafWithTransfers
