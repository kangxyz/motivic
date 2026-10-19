/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.FilteredHomology
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ExtRightDerived
public import Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.Basic

/-! # Original ordinary Ext and actual right-derived neighborhood sections -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf
variable {S T : Scheme.{u}} (b : T ⟶ S) (V : EtaleSeparatedFiniteType S)

/-- The original free abelian sheaf represents actual pulled-back neighborhood sections. -/
def pulledBackNeighborhoodSectionsRepresented :
    preadditiveCoyoneda.obj (Opposite.op
      (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
        (nisnevichTopology T) ((baseChange b).obj V))) ≅
      pulledBackNeighborhoodSections b V :=
  NatIso.ofComponents (fun F =>
    (Hypercohomology.sectionsAddEquiv (nisnevichTopology T)
      ((baseChange b).obj V) F).toAddCommGrpIso) (by intros; ext; rfl)

/-- The explicit representing equivalence induces an isomorphism of derived section functors. -/
def pulledBackNeighborhoodDerivedSectionsRepresented (n : ℕ) :
    (preadditiveCoyoneda.obj (Opposite.op
      (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
        (nisnevichTopology T) ((baseChange b).obj V)))).rightDerived n ≅
      (pulledBackNeighborhoodSections b V).rightDerived n where
  hom := NatTrans.rightDerived (pulledBackNeighborhoodSectionsRepresented b V).hom n
  inv := NatTrans.rightDerived (pulledBackNeighborhoodSectionsRepresented b V).inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, Iso.hom_inv_id,
    NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, Iso.inv_hom_id,
    NatTrans.rightDerived_id]

variable [HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})]
  {F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}} (I : InjectiveResolution F)

/-- Original ordinary cohomology, not a replacement theory, computes actual derived sections. -/
def ordinaryNeighborhoodDerivedSections (n : ℕ) :
    LargeCohomology.H.{u + 1, u + 1, u, u + 1}
      (nisnevichTopology T) F n ((baseChange b).obj V) ≃+
        (((pulledBackNeighborhoodSections b V).rightDerived n).obj F) :=
  (I.extRightDerivedAddEquiv
    (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
      (nisnevichTopology T) ((baseChange b).obj V)) n).trans
    ((pulledBackNeighborhoodDerivedSectionsRepresented b V n).app F).addCommGroupIsoToAddEquiv

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
