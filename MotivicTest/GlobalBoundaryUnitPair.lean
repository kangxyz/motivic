/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.GlobalBoundaryUnitPair

/-! Different prescribed units on the same bundle, without a rational-function hypothesis. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.QuasiCoherent
universe u
example (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C Z : Scheme.{u}} [IsLocallyNoetherian C]
    (k : C ⟶ ProjectiveSpace R ι) [IsFinite k]
    (z : Z ⟶ C) [IsClosedImmersion z]
    (M : C.Modules) (hM : affineLocallyFiniteType C M)
    (e₀ e₁ : (Scheme.Modules.pullback z).obj M ≅ SheafOfModules.unit Z.ringCatSheaf) :=
  Scheme.CoherentGraph.finiteMap_exists_global_boundary_unit_pair R ι n e k z M M hM hM e₀ e₁

#print axioms AlgebraicGeometry.Scheme.CoherentGraph.finiteMap_exists_global_boundary_unit_pair
