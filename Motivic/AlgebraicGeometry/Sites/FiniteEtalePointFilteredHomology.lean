/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleDerivedPointFiber
public import Mathlib.Algebra.Homology.Functor

/-!
# Filtered homology of actual pulled-back neighborhoods

This computes point fibers using a filtered colimit of the homology functor of
an actual neighborhood diagram. Identification of these homology groups with
ordinary Ext, and scheme-theoretic henselization continuity, are separate steps.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.FiniteEtaleSite
variable {S T : Scheme.{u}} (b : T ⟶ S)
  (Φ : (nisnevichTopology S).Point.{u + 1})

/-- The actual coefficient functor on the filtered category of point neighborhoods. -/
def directImagePointDiagramFunctor :
    Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1} ⥤
      (Φ.fiber.Elementsᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  directImage b ⋙ sheafToPresheaf _ _ ⋙
    (Functor.whiskeringLeft _ _ _).obj (Functor.Elements.π Φ.fiber).op

instance : (directImagePointDiagramFunctor b Φ).Additive := by
  dsimp only [directImagePointDiagramFunctor]
  infer_instance

variable {F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}}
  (I : InjectiveResolution F)

/-- The three-term resolution on the actual geometrically pulled-back neighborhoods. -/
def directImageResolutionNeighborhoodStep (n : ℕ) :
    ShortComplex (Φ.fiber.Elementsᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  (I.cocomplex.sc n).map (directImagePointDiagramFunctor b Φ)

/-- Filtered colimits commute with homology for this actual neighborhood resolution. -/
def derivedDirectImagePointFilteredHomologyIso (n : ℕ) :
    Φ.sheafFiber.obj (((directImage b).rightDerived n).obj F) ≅
      colimit (directImageResolutionNeighborhoodStep b Φ I n).homology :=
  derivedDirectImagePointFiberIso b Φ I n ≪≫
    (directImageResolutionNeighborhoodStep b Φ I n).mapHomologyIso colim

/-- Each member of the homology diagram is the homology of its actual section groups. -/
def directImageResolutionNeighborhoodHomologyIso (n : ℕ) (V : Φ.fiber.Elementsᵒᵖ) :
    ((directImageResolutionNeighborhoodStep b Φ I n).homology).obj V ≅
      ((directImageResolutionNeighborhoodStep b Φ I n).map
        ((CategoryTheory.evaluation _ _).obj V)).homology :=
  ((directImageResolutionNeighborhoodStep b Φ I n).mapHomologyIso
    ((CategoryTheory.evaluation _ _).obj V)).symm

/-- The middle group is literally sections on the geometrically pulled-back neighborhood. -/
@[simp]
theorem directImageResolutionNeighborhoodStep_X₂_obj (n : ℕ)
    (V : FiniteEtaleSite S) (v : Φ.fiber.obj V) :
    (directImageResolutionNeighborhoodStep b Φ I n).X₂.obj
        (Opposite.op (Φ.fiber.elementsMk V v)) =
      (I.cocomplex.X n).obj.obj (Opposite.op ((baseChange b).obj V)) := rfl

/-- Sections on an actual geometrically pulled-back finite-type étale neighborhood. -/
def pulledBackNeighborhoodSections (V : FiniteEtaleSite S) :
    Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  sheafToPresheaf _ _ ⋙
    (CategoryTheory.evaluation _ _).obj (Opposite.op ((baseChange b).obj V))

instance (V : FiniteEtaleSite S) : (pulledBackNeighborhoodSections b V).Additive := by
  dsimp only [pulledBackNeighborhoodSections]
  infer_instance

/-- The neighborhood homology is the genuine right-derived section functor.
This is not yet a comparison with the project's ordinary derived-category `Ext`. -/
def derivedNeighborhoodSectionsIso (n : ℕ)
    (V : FiniteEtaleSite S) (v : Φ.fiber.obj V) :
    (((pulledBackNeighborhoodSections b V).rightDerived n).obj F) ≅
      ((directImageResolutionNeighborhoodStep b Φ I n).homology).obj
        (Opposite.op (Φ.fiber.elementsMk V v)) :=
  I.isoRightDerivedObj (pulledBackNeighborhoodSections b V) n ≪≫
    (directImageResolutionNeighborhoodHomologyIso b Φ I n
      (Opposite.op (Φ.fiber.elementsMk V v))).symm

/-- Coefficient naturality retains the map of the actual neighborhood homology diagrams. -/
@[reassoc]
theorem derivedDirectImagePointFilteredHomologyIso_naturality
    {G : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}} (f : F ⟶ G)
    (J : InjectiveResolution G) (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    Φ.sheafFiber.map (((directImage b).rightDerived n).map f) ≫
        (derivedDirectImagePointFilteredHomologyIso b Φ J n).hom =
      (derivedDirectImagePointFilteredHomologyIso b Φ I n).hom ≫
        colim.map (ShortComplex.homologyMap
          ((directImagePointDiagramFunctor b Φ).mapShortComplex.map
            ((HomologicalComplex.shortComplexFunctor _ _ n).map φ))) := by
  dsimp only [derivedDirectImagePointFilteredHomologyIso, Iso.trans_hom]
  rw [← Category.assoc, derivedDirectImagePointFiberIso_naturality b Φ I f J φ hφ n,
    Category.assoc, Category.assoc]
  congr 1
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((directImagePointDiagramFunctor b Φ).mapShortComplex.map
      ((HomologicalComplex.shortComplexFunctor _ _ n).map φ)) colim

end Motivic.FiniteEtaleSite
