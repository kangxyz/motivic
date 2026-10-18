/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.RankZeroCylinderColimit
public import Motivic.Cohomology.A1.PointedMarkedCylinderComparison
public import Motivic.Cohomology.RelativeGenericBaseCylinderZero

/-! # Positive cylinder germs at arbitrary rank-zero marked points

The whole-cylinder generic-base producer is discharged for HI Nisnevich sheaves
with transfers. Every group, field mark, neighborhood index and higher-image
fiber is the original one. No strict A1 theorem at positive local rank is claimed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u

namespace Motivic.FiniteEtaleSite

variable {k : Type u} [Field k] (F : SheafWithTransfers.{u + 1} k)
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- All positive original cylinder germs vanish at an arbitrary field-valued
rank-zero center. The generic-base vanishing input is proved, not assumed. -/
theorem pointedCylinderColimit_isZero_of_rank_zero (hF : F.obj.IsA1Invariant) (n : ℕ)
    (X : SmoothSite (Spec (.of k))) (K : Type u) [Field K]
    (b : Spec (.of K) ⟶ X.left) (p : Spec (.of K))
    (hd : ringKrullDim (X.left.presheaf.stalk (b p)) = 0) :
    IsZero (colimit (pointedCylinderValues (.of k) (relativeFieldPoint b K (𝟙 _))
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) (n + 1))
      (pointedBase (.of k) (relativeFieldPoint b K (𝟙 _))))) := by
  apply pointedCylinderColimit_isZero_of_rank_zero_generic_open_zero X K b p _ hd
  intro Y _ _ s
  obtain ⟨O, _hO, hη, hz⟩ :=
    SheafCohomology.exists_generic_base_cylinder_positive_zero F hF n Y s
  exact ⟨O, hη, hz⟩

/-- The rank-zero starting case for local-rank induction uses the actual residue
point of each original smooth object and its entire neighborhood diagram. -/
theorem residueCylinderColimit_isZero_of_rank_zero (hF : F.obj.IsA1Invariant) (n : ℕ)
    (X : SmoothSite (Spec (.of k))) (x : X.left)
    (hd : ringKrullDim (X.left.presheaf.stalk x) = 0) :
    IsZero (colimit (pointedCylinderValues (.of k) (X := X) (residuePoint X.left x)
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) (n + 1))
      (pointedBase (.of k) (X := X) (residuePoint X.left x)))) := by
  apply pointedCylinderColimit_isZero_of_rank_zero F hF n X (X.left.residueField x)
    (X.left.fromSpecResidueField x) (IsLocalRing.closedPoint (X.left.residueField x))
  exact (congrArg (fun z : X.left => ringKrullDim (X.left.presheaf.stalk z))
    (X.left.fromSpecResidueField_apply x
      (IsLocalRing.closedPoint (X.left.residueField x)))).trans hd

/-- The original positive higher direct image has zero fiber at every
field-valued rank-zero center, via the original cylinder comparison. -/
theorem projectionPointFiber_isZero_of_rank_zero (hF : F.obj.IsA1Invariant) (n : ℕ)
    (X : SmoothSite (Spec (.of k))) (K : Type u) [Field K]
    (b : Spec (.of K) ⟶ X.left) (p : Spec (.of K))
    (hd : ringKrullDim (X.left.presheaf.stalk (b p)) = 0)
    [HasExt.{u + 1}
      (Sheaf (nisnevichTopology (SmoothSite.a1Cylinder (.of k) X).left)
        AddCommGrpCat.{u + 1})] :
    IsZero ((relativeFieldPoint b K (𝟙 _)).sheafFiber.obj
      (((directImage (SmoothSite.a1Projection (.of k) X).left).rightDerived (n + 1)).obj
        ((restrict (SmoothSite.a1Cylinder (.of k) X) AddCommGrpCat).obj
          ((SheafWithTransfers.toSheaf k).obj F)))) :=
  (pointedCylinderColimit_isZero_of_rank_zero F hF n X K b p hd).of_iso
    (pointedCylinderColimitFiberIso (.of k) X (relativeFieldPoint b K (𝟙 _))
      ((SheafWithTransfers.toSheaf k).obj F) (n + 1)).symm

/-- Every rank-zero marker of an actual test neighborhood has zero positive
higher-image fiber on the original base, without a derived etale base-change theorem. -/
theorem markedProjectionFiber_isZero_of_rank_zero (hF : F.obj.IsA1Invariant) (n : ℕ)
    (X : SmoothSite (Spec (.of k))) (V : FiniteEtaleSite X.left) (x : V.left)
    (hd : ringKrullDim (V.left.presheaf.stalk x) = 0)
    [HasExt.{u + 1}
      (Sheaf (nisnevichTopology (SmoothSite.a1Cylinder (.of k) X).left)
        AddCommGrpCat.{u + 1})] :
    IsZero ((markedResiduePoint V x).sheafFiber.obj
      (((directImage (SmoothSite.a1Projection (.of k) X).left).rightDerived (n + 1)).obj
        ((restrict (SmoothSite.a1Cylinder (.of k) X) AddCommGrpCat).obj
          ((SheafWithTransfers.toSheaf k).obj F)))) :=
  markedProjectionFiber_isZero_of_cylinderColimit (.of k) X V x
    ((SheafWithTransfers.toSheaf k).obj F) (n + 1)
      (residueCylinderColimit_isZero_of_rank_zero F hF n ((toSmoothSite X).obj V) x hd)

end Motivic.FiniteEtaleSite
