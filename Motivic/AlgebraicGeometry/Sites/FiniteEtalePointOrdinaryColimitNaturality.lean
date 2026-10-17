/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtalePointOrdinaryColimit
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOrdinaryDerivedSectionsCoefficient

/-! # Coefficient naturality of genuine point-fiber ordinary cohomology continuity -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.FiniteEtaleSite
variable {S T : Scheme.{u}} (b : T ⟶ S)
  (Φ : (nisnevichTopology S).Point.{u + 1})
  {F G : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}} (g : F ⟶ G)
  (I : InjectiveResolution F) (J : InjectiveResolution G)
  (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = g ≫ J.ι.f 0)

/-- The actual coefficient map on the resolution-neighborhood homology diagram. -/
def neighborhoodResolutionHomologyMap (n : ℕ) :
    (directImageResolutionNeighborhoodStep b Φ I n).homology ⟶
      (directImageResolutionNeighborhoodStep b Φ J n).homology :=
  ShortComplex.homologyMap ((directImagePointDiagramFunctor b Φ).mapShortComplex.map
    ((HomologicalComplex.shortComplexFunctor _ _ n).map φ))

/-- Evaluating the actual resolution-homology diagram respects coefficient comparison maps. -/
include hφ in
@[reassoc]
theorem derivedNeighborhoodSectionsIso_coeff (n : ℕ) (V : Φ.fiber.Elementsᵒᵖ) :
    ((pulledBackNeighborhoodSections b V.unop.obj).rightDerived n).map g ≫
        (derivedNeighborhoodSectionsIso b Φ J n V.unop.obj V.unop.val).hom =
      (derivedNeighborhoodSectionsIso b Φ I n V.unop.obj V.unop.val).hom ≫
        (neighborhoodResolutionHomologyMap b Φ I J φ n).app V := by
  dsimp only [derivedNeighborhoodSectionsIso, directImageResolutionNeighborhoodHomologyIso,
    Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, I.isoRightDerivedObj_hom_naturality g J φ hφ,
    Category.assoc, Category.assoc]
  apply congrArg (fun a => (I.isoRightDerivedObj
    (pulledBackNeighborhoodSections b V.unop.obj) n).hom ≫ a)
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((directImagePointDiagramFunctor b Φ).mapShortComplex.map
      ((HomologicalComplex.shortComplexFunctor _ _ n).map φ))
    ((CategoryTheory.evaluation _ _).obj V)

variable [HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})]

/-- The coefficient morphism in the original ordinary cohomology diagram. -/
def ordinaryPointCohomologyMap (n : ℕ) :
    ordinaryPointCohomologyDiagram b Φ (F := F) n ⟶
      ordinaryPointCohomologyDiagram b Φ (F := G) n :=
  Functor.whiskerLeft ((Functor.Elements.π Φ.fiber).op ⋙ (baseChange b).op)
    ((SheafCohomology.presheafFunctor (nisnevichTopology T) n).map g)

/-- The diagram comparison commutes with original ordinary coefficient maps. -/
include hφ in
@[reassoc]
theorem ordinaryPointHomologyIso_naturality (n : ℕ) :
    ordinaryPointCohomologyMap b Φ g n ≫ (ordinaryPointHomologyIso b Φ J n).hom =
      (ordinaryPointHomologyIso b Φ I n).hom ≫
        neighborhoodResolutionHomologyMap b Φ I J φ n := by
  ext V x
  change (derivedNeighborhoodSectionsIso b Φ J n V.unop.obj V.unop.val).hom
    (ordinaryNeighborhoodDerivedSections b V.unop.obj J n
      (((SheafCohomology.presheafFunctor (nisnevichTopology T) n).map g).app
        (Opposite.op ((baseChange b).obj V.unop.obj)) x)) = _
  rw [ordinaryNeighborhoodDerivedSections_naturality_right b V.unop.obj g I J φ hφ]
  exact ConcreteCategory.congr_hom (derivedNeighborhoodSectionsIso_coeff b Φ g I J φ hφ n V)
    (ordinaryNeighborhoodDerivedSections b V.unop.obj I n x)

/-- The final comparison preserves actual derived and original ordinary coefficient maps. -/
include hφ in
@[reassoc]
theorem derivedDirectImagePointOrdinaryColimitIso_naturality (n : ℕ) :
    Φ.sheafFiber.map (((directImage b).rightDerived n).map g) ≫
        (derivedDirectImagePointOrdinaryColimitIso b Φ J n).hom =
      (derivedDirectImagePointOrdinaryColimitIso b Φ I n).hom ≫
        colim.map (ordinaryPointCohomologyMap b Φ g n) := by
  dsimp only [derivedDirectImagePointOrdinaryColimitIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, derivedDirectImagePointFilteredHomologyIso_naturality b Φ I g J φ hφ,
    Category.assoc, Category.assoc]
  apply congrArg (fun a => (derivedDirectImagePointFilteredHomologyIso b Φ I n).hom ≫ a)
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply (cancel_epi (ordinaryPointHomologyIso b Φ I n).hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← ordinaryPointHomologyIso_naturality b Φ g I J φ hφ n,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Motivic.FiniteEtaleSite
