/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.DerivedSections
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ExtRightDerivedCoefficient

/-! # Genuine coefficient naturality of ordinary derived neighborhood sections -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf
variable {S T : Scheme.{u}} (b : T ⟶ S) (V : EtaleSeparatedFiniteType S)
  {F G : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}} (g : F ⟶ G)

/-- The section-representation square on coefficients, in elementwise form. -/
theorem pulledBackNeighborhoodDerivedSectionsRepresented_coeff_apply (n : ℕ)
    (y : ((preadditiveCoyoneda.obj (Opposite.op
      (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
        (nisnevichTopology T) ((baseChange b).obj V)))).rightDerived n).obj F) :
    ((pulledBackNeighborhoodDerivedSectionsRepresented b V n).app G).addCommGroupIsoToAddEquiv
      (((preadditiveCoyoneda.obj (Opposite.op
        (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
          (nisnevichTopology T) ((baseChange b).obj V)))).rightDerived n).map g y) =
      ((pulledBackNeighborhoodSections b V).rightDerived n).map g
        (((pulledBackNeighborhoodDerivedSectionsRepresented b V n).app
          F).addCommGroupIsoToAddEquiv y) :=
  ConcreteCategory.congr_hom
    ((pulledBackNeighborhoodDerivedSectionsRepresented b V n).hom.naturality g) y

attribute [local irreducible] InjectiveResolution.extRightDerivedAddEquiv
variable [HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})]
  (I : InjectiveResolution F) (J : InjectiveResolution G)

/-- Original ordinary cohomology coefficient maps agree with the genuine derived section maps. -/
theorem ordinaryNeighborhoodDerivedSections_naturality_right
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = g ≫ J.ι.f 0)
    (n : ℕ) (x : LargeCohomology.H.{u + 1, u + 1, u, u + 1}
      (nisnevichTopology T) F n ((baseChange b).obj V)) :
    ordinaryNeighborhoodDerivedSections b V J n
      (((LargeCohomology.presheafFunctor (nisnevichTopology T) n).map g).app
        (Opposite.op ((baseChange b).obj V)) x) =
      ((pulledBackNeighborhoodSections b V).rightDerived n).map g
        (ordinaryNeighborhoodDerivedSections b V I n x) := by
  change ordinaryNeighborhoodDerivedSections b V J n
    (x.comp (Abelian.Ext.mk₀ g) (add_zero n)) = _
  dsimp only [ordinaryNeighborhoodDerivedSections, AddEquiv.trans_apply]
  erw [I.extRightDerivedAddEquiv_naturality_right J g φ hφ
    (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
      (nisnevichTopology T) ((baseChange b).obj V)) n x]
  exact pulledBackNeighborhoodDerivedSectionsRepresented_coeff_apply b V g n _

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
