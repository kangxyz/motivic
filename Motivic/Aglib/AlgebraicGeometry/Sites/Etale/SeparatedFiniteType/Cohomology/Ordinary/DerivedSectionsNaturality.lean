/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.DerivedSections
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ExtRightDerivedFunctoriality
public import Motivic.Aglib.CategoryTheory.Sites.FreeAbelianSheafPushout

/-! # Original restriction maps in the ordinary derived-section comparison -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf
variable {S T : Scheme.{u}} (b : T ⟶ S) {V W : EtaleSeparatedFiniteType S} (f : V ⟶ W)

/-- Restriction uses the original geometric base-change morphism. -/
def pulledBackNeighborhoodSectionsMap :
    pulledBackNeighborhoodSections b W ⟶ pulledBackNeighborhoodSections b V :=
  Functor.whiskerLeft (sheafToPresheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})
    ((CategoryTheory.evaluation _ _).map ((baseChange b).map f).op)

/-- The explicit representing equivalences respect the original restriction maps. -/
@[reassoc]
theorem pulledBackNeighborhoodSectionsRepresented_naturality :
    preadditiveCoyoneda.map
        (((Hypercohomology.freeAbelianSheafFunctor (nisnevichTopology T)).map
          ((baseChange b).map f)).op) ≫ (pulledBackNeighborhoodSectionsRepresented b V).hom =
      (pulledBackNeighborhoodSectionsRepresented b W).hom ≫
        pulledBackNeighborhoodSectionsMap b f := by
  ext F h
  exact Hypercohomology.sectionsEquiv_restriction (nisnevichTopology T)
    ((baseChange b).map f) F h

/-- Taking right derived functors preserves the actual section-representation square. -/
@[reassoc]
theorem pulledBackNeighborhoodDerivedSectionsRepresented_naturality (n : ℕ) :
    NatTrans.rightDerived (preadditiveCoyoneda.map
        (((Hypercohomology.freeAbelianSheafFunctor (nisnevichTopology T)).map
          ((baseChange b).map f)).op)) n ≫
        (pulledBackNeighborhoodDerivedSectionsRepresented b V n).hom =
      (pulledBackNeighborhoodDerivedSectionsRepresented b W n).hom ≫
        NatTrans.rightDerived (pulledBackNeighborhoodSectionsMap b f) n := by
  dsimp only [pulledBackNeighborhoodDerivedSectionsRepresented]
  rw [← NatTrans.rightDerived_comp, pulledBackNeighborhoodSectionsRepresented_naturality,
    NatTrans.rightDerived_comp]

/-- Elementwise form with no Ext expression exposed during elaboration. -/
theorem pulledBackNeighborhoodDerivedSectionsRepresented_naturality_apply (n : ℕ)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})
    (y : ((preadditiveCoyoneda.obj (Opposite.op
      (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
        (nisnevichTopology T) ((baseChange b).obj W)))).rightDerived n).obj F) :
    ((pulledBackNeighborhoodDerivedSectionsRepresented b V n).app F).addCommGroupIsoToAddEquiv
      ((NatTrans.rightDerived (preadditiveCoyoneda.map
        (((Hypercohomology.freeAbelianSheafFunctor (nisnevichTopology T)).map
          ((baseChange b).map f)).op)) n).app F y) =
      (NatTrans.rightDerived (pulledBackNeighborhoodSectionsMap b f) n).app F
        (((pulledBackNeighborhoodDerivedSectionsRepresented b W n).app
          F).addCommGroupIsoToAddEquiv y) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (pulledBackNeighborhoodDerivedSectionsRepresented_naturality b f n) F) y

attribute [local irreducible] InjectiveResolution.extRightDerivedAddEquiv

variable [HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})]
  {F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}} (I : InjectiveResolution F)

/-- Original ordinary cohomology restriction matches the actual derived section map. -/
theorem ordinaryNeighborhoodDerivedSections_naturality_left (n : ℕ)
    (x : LargeCohomology.H.{u + 1, u + 1, u, u + 1}
      (nisnevichTopology T) F n ((baseChange b).obj W)) :
    ordinaryNeighborhoodDerivedSections b V I n
      ((LargeCohomology.presheaf (nisnevichTopology T) F n).map
        ((baseChange b).map f).op x) =
      (NatTrans.rightDerived (pulledBackNeighborhoodSectionsMap b f) n).app F
        (ordinaryNeighborhoodDerivedSections b W I n x) := by
  dsimp only [ordinaryNeighborhoodDerivedSections, AddEquiv.trans_apply]
  rw [LargeCohomology.restriction_apply]
  erw [I.extRightDerivedAddEquiv_naturality_left
    ((Hypercohomology.freeAbelianSheafFunctor (nisnevichTopology T)).map
      ((baseChange b).map f)) n x]
  convert! pulledBackNeighborhoodDerivedSectionsRepresented_naturality_apply b f n F
    (I.extRightDerivedAddEquiv
      (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
        (nisnevichTopology T) ((baseChange b).obj W)) n x) using 1

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
