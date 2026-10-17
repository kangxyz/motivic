/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleDerivedPointFiber
public import Lean.Util.CollectAxioms

/-! The resolution-level comparison at a literal residue-field point, not a fake smooth object. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace MotivicTest.FiniteEtaleDerivedPointFiber
open Motivic.FiniteEtaleSite
variable {S T : Scheme.{u}} (b : T ⟶ S) (x : S)
  {F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}} (I : InjectiveResolution F)

/-- The actual inverse-image evaluation of the higher direct image is computed by
homology of the original neighborhood-fiber resolution groups. -/
def actual_residue_higherDirectImage (n : ℕ) :
    ((inverseImage (S.fromSpecResidueField x)).obj
      (((directImage b).rightDerived n).obj F)).obj.obj
        (Opposite.op (fieldObject (S.residueField x) (𝟙 _))) ≅
      (directImageResolutionFiberStep b
        (relativeFieldPoint (S.fromSpecResidueField x) (S.residueField x) (𝟙 _)) I n).homology :=
  ((relativeFieldPointInverseImageIso (S.fromSpecResidueField x)
    (S.residueField x) (𝟙 _)).app (((directImage b).rightDerived n).obj F)).symm ≪≫
    derivedDirectImagePointFiberIso b _ I n

open Lean in
run_cmd do
  for name in #[``actual_residue_higherDirectImage,
      ``Motivic.FiniteEtaleSite.sheaf_enoughInjectives,
      ``Motivic.FiniteEtaleSite.sheaf_isGrothendieckAbelian,
      ``Motivic.FiniteEtaleSite.derivedDirectImagePointFiberIso_naturality,
      ``Motivic.FiniteEtaleSite.directImagePointInclusion_naturality,
      ``Motivic.FiniteEtaleSite.directImagePointColimitIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual residue-field inverse image and resolution-level point fibers: standard axioms."

end MotivicTest.FiniteEtaleDerivedPointFiber
