/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtalePointOrdinaryColimitNaturality
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOrdinaryDerivedSectionsCoefficient
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Lean.Util.CollectAxioms

/-! Actual residue-field inverse image and original ordinary cohomology colimit. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace MotivicTest.FiniteEtalePointOrdinaryColimit
open Motivic Motivic.FiniteEtaleSite
variable {S T : Scheme.{u}} (b : T ⟶ S) (x : S)

local instance : HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

/-- Literal residue-field inverse image and original ordinary Ext diagram. -/
def actual_residue_ordinary_colimit
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) (n : ℕ) :
    ((inverseImage (S.fromSpecResidueField x)).obj
      (((directImage b).rightDerived n).obj F)).obj.obj
        (Opposite.op (fieldObject (S.residueField x) (𝟙 _))) ≅
      colimit (ordinaryPointCohomologyDiagram b
        (relativeFieldPoint (S.fromSpecResidueField x) (S.residueField x) (𝟙 _)) (F := F) n) :=
  ((relativeFieldPointInverseImageIso (S.fromSpecResidueField x)
    (S.residueField x) (𝟙 _)).app (((directImage b).rightDerived n).obj F)).symm ≪≫
    derivedDirectImagePointOrdinaryColimitIso b _ (injectiveResolution F) n

/-- Coefficient naturality uses genuine resolution comparison maps, not a new hypothesis. -/
theorem actual_point_ordinary_colimit_naturality
    (Φ : (nisnevichTopology S).Point.{u + 1})
    {F G : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}} (g : F ⟶ G) (n : ℕ) :
    Φ.sheafFiber.map (((directImage b).rightDerived n).map g) ≫
        (derivedDirectImagePointOrdinaryColimitIso b Φ (injectiveResolution G) n).hom =
      (derivedDirectImagePointOrdinaryColimitIso b Φ (injectiveResolution F) n).hom ≫
        colim.map (ordinaryPointCohomologyMap b Φ g n) :=
  derivedDirectImagePointOrdinaryColimitIso_naturality b Φ g
    (injectiveResolution F) (injectiveResolution G)
    (InjectiveResolution.desc g (injectiveResolution G) (injectiveResolution F))
    (InjectiveResolution.desc_commutes_zero g (injectiveResolution G) (injectiveResolution F)) n

open Lean in
run_cmd do
  for name in #[``actual_residue_ordinary_colimit,
      ``actual_point_ordinary_colimit_naturality,
      ``Motivic.FiniteEtaleSite.ordinaryPointHomologyIso,
      ``Motivic.FiniteEtaleSite.derivedDirectImagePointOrdinaryColimitIso_naturality,
      ``Motivic.FiniteEtaleSite.ordinaryNeighborhoodDerivedSections_naturality_left,
      ``Motivic.FiniteEtaleSite.ordinaryNeighborhoodDerivedSections_naturality_right] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual residue fibers and original ordinary cohomology colimits: standard axioms."

end MotivicTest.FiniteEtalePointOrdinaryColimit
