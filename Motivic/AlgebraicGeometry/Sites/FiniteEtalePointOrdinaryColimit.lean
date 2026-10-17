/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOrdinaryDerivedSectionsNaturality

/-! # Actual higher direct-image point fibers as colimits of original ordinary cohomology -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.FiniteEtaleSite
variable {S T : Scheme.{u}} (b : T ⟶ S)
  (Φ : (nisnevichTopology S).Point.{u + 1})
  {F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}} (I : InjectiveResolution F)

/-- The evaluated resolution comparison respects actual morphisms of point neighborhoods. -/
@[reassoc]
theorem derivedNeighborhoodSectionsIso_naturality (n : ℕ)
    {V W : Φ.fiber.Elementsᵒᵖ} (f : V ⟶ W) :
    (NatTrans.rightDerived (pulledBackNeighborhoodSectionsMap b
        ((Functor.Elements.π Φ.fiber).map f.unop)) n).app F ≫
        (derivedNeighborhoodSectionsIso b Φ I n W.unop.obj W.unop.val).hom =
      (derivedNeighborhoodSectionsIso b Φ I n V.unop.obj V.unop.val).hom ≫
        (directImageResolutionNeighborhoodStep b Φ I n).homology.map f := by
  rw [I.rightDerived_app_eq]
  dsimp only [derivedNeighborhoodSectionsIso, directImageResolutionNeighborhoodHomologyIso,
    Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  apply (cancel_epi (I.isoRightDerivedObj
    (pulledBackNeighborhoodSections b V.unop.obj) n).hom).2
  change ShortComplex.homologyMap
      ((directImageResolutionNeighborhoodStep b Φ I n).mapNatTrans
        ((CategoryTheory.evaluation _ _).map f)) ≫ _ = _
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp

variable [HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})]

/-- The original ordinary cohomology presheaf restricted along geometric pullback. -/
def ordinaryPointCohomologyDiagram (n : ℕ) : Φ.fiber.Elementsᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.Elements.π Φ.fiber).op ⋙ (baseChange b).op ⋙
    SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1} (nisnevichTopology T) F n

/-- Actual ordinary restriction maps agree with the neighborhood resolution-homology diagram. -/
def ordinaryPointHomologyIso (n : ℕ) :
    ordinaryPointCohomologyDiagram b Φ (F := F) n ≅
      (directImageResolutionNeighborhoodStep b Φ I n).homology :=
  NatIso.ofComponents (fun V =>
    (ordinaryNeighborhoodDerivedSections b V.unop.obj I n).toAddCommGrpIso ≪≫
      derivedNeighborhoodSectionsIso b Φ I n V.unop.obj V.unop.val) (by
    intro V W f
    ext x
    change (derivedNeighborhoodSectionsIso b Φ I n W.unop.obj W.unop.val).hom
      (ordinaryNeighborhoodDerivedSections b W.unop.obj I n
        ((SheafCohomology.presheaf (nisnevichTopology T) F n).map
          ((baseChange b).map ((Functor.Elements.π Φ.fiber).map f.unop)).op x)) = _
    erw [ordinaryNeighborhoodDerivedSections_naturality_left]
    exact ConcreteCategory.congr_hom (derivedNeighborhoodSectionsIso_naturality b Φ I n f)
      (ordinaryNeighborhoodDerivedSections b V.unop.obj I n x))

/-- The genuine point fiber of the genuine higher direct image is a filtered colimit of the
original ordinary cohomology groups of the actual geometrically pulled-back neighborhoods. -/
def derivedDirectImagePointOrdinaryColimitIso (n : ℕ) :
    Φ.sheafFiber.obj (((directImage b).rightDerived n).obj F) ≅
      colimit (ordinaryPointCohomologyDiagram b Φ (F := F) n) :=
  derivedDirectImagePointFilteredHomologyIso b Φ I n ≪≫
    colim.mapIso (ordinaryPointHomologyIso b Φ I n).symm

end Motivic.FiniteEtaleSite
