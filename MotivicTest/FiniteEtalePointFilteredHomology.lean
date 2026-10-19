/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.FilteredHomology
public import Lean.Util.CollectAxioms

/-! The resolution-level comparison at a literal residue-field point, not a fake smooth object. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace MotivicTest.FiniteEtalePointFilteredHomology
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {S T : Scheme.{u}} (b : T ⟶ S) (x : S)
  {F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}} (I : InjectiveResolution F)

/-- The actual inverse-image evaluation of the higher direct image is computed by
homology of the original neighborhood-fiber resolution groups. -/
def actual_residue_filteredHomology (n : ℕ) :
    ((inverseImage (S.fromSpecResidueField x)).obj
      (((directImage b).rightDerived n).obj F)).obj.obj
        (Opposite.op (fieldObject (S.residueField x) (𝟙 _))) ≅
      colimit (directImageResolutionNeighborhoodStep b
        (relativeFieldPoint (S.fromSpecResidueField x) (S.residueField x) (𝟙 _)) I n).homology :=
  ((relativeFieldPointInverseImageIso (S.fromSpecResidueField x)
    (S.residueField x) (𝟙 _)).app (((directImage b).rightDerived n).obj F)).symm ≪≫
    derivedDirectImagePointFilteredHomologyIso b _ I n

open Lean in
run_cmd do
  for name in #[``actual_residue_filteredHomology,
      ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.sheaf_enoughInjectives,
      ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.sheaf_isGrothendieckAbelian,
      ``derivedDirectImagePointFilteredHomologyIso_naturality,
      ``directImageResolutionNeighborhoodHomologyIso,
      ``derivedNeighborhoodSectionsIso,
      ``directImageResolutionNeighborhoodStep_X₂_obj,
      ``directImagePointInclusion_naturality,
      ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.directImagePointColimitIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual residue-field inverse image and filtered neighborhood homology: standard axioms."

end MotivicTest.FiniteEtalePointFilteredHomology
