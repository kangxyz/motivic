/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.GlobalBoundarySectionMaps

/-! Actual Serre-produced sheaf map with exact whole-boundary pullback value. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent AlgebraicGeometry.Scheme.CoherentGraph
universe u
example (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {C Z : Scheme.{u}} [IsLocallyNoetherian C]
    (a : C ⟶ ProjectiveSpace R ι) [IsFinite a]
    (z : Z ⟶ C) [IsClosedImmersion z]
    (M : C.Modules) (hM : affineLocallyFiniteType C M) :=
  finiteMap_exists_global_section_map R ι n e a z M hM
#print axioms AlgebraicGeometry.Scheme.CoherentGraph.finiteMap_exists_global_section_map
#print axioms AlgebraicGeometry.Scheme.CoherentGraph.pullback_section_of_boundary_value
