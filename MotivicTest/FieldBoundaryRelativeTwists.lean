/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.FieldBoundaryRelativeTwists

/-! # Original relative boundary-coefficient unit consumer -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.CoherentGraph

namespace Motivic.MotivicTest.FieldBoundaryRelativeTwists
universe u

/-- The original coefficient sheaf has a genuine generating section on the fixed full boundary. -/
theorem actual_relative_boundary_unit
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (ι : Type u) {Z W C : Scheme.{u}}
    (g : Z ⟶ ProjectiveSpace k ι) [IsFinite (g ≫ toSpec k ι)]
    (b : W ⟶ Z) (a : C ⟶ ProjectiveSpace R ι) (z : W ⟶ C)
    (ha : (z ≫ a) ≫ ProjectiveSpace.map (algebraMap k R) ι = b ≫ g) (n : ℕ) :
    let Q := (moduleTensorLeftFunctor W
      ((Modules.pullback z).obj ((Modules.pullback a).obj (twistingSheaf R ι (n : ℤ))))).obj
        ((Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf))
    ∃ σ : Γ(Q, ⊤), IsIso ((unitHomGlobalSectionsEquiv W Q).symm σ) :=
  exists_fieldBoundaryRelativeCoefficient_unitSection k R (algebraMap k R) ι g b a z ha n

open Lean in
run_cmd do
  for name in #[``fieldBoundaryRelativeTwistIso, ``fieldBoundaryRelativeCoefficientIso,
      ``exists_fieldBoundaryRelativeCoefficient_unitSection, ``actual_relative_boundary_unit] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual relative full-boundary units use only standard foundations."

end Motivic.MotivicTest.FieldBoundaryRelativeTwists
