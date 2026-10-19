/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Sections.FixedFieldSectionPair

/-! Exact global module-map lifts on the unchanged affine source. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent AlgebraicGeometry.Scheme.CoherentGraph
universe u
example (k R : Type u) [Field k] [CommRing R] [IsNoetherianRing R]
    (f : k →+* R) (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C Z W : Scheme.{u}} [IsLocallyNoetherian C]
    (a : C ⟶ ProjectiveSpace R ι) [IsFinite a]
    (z : W ⟶ C) [IsClosedImmersion z]
    (g : Z ⟶ ProjectiveSpace k ι) [IsFinite (g ≫ toSpec k ι)]
    (b : W ⟶ Z) (ha : (z ≫ a) ≫ ProjectiveSpace.map f ι = b ≫ g)
    (M N : C.Modules) (hM : affineLocallyFiniteType C M) (hN : affineLocallyFiniteType C N)
    (eM : (Scheme.Modules.pullback z).obj M ≅ SheafOfModules.unit W.ringCatSheaf)
    (eN : (Scheme.Modules.pullback z).obj N ≅ SheafOfModules.unit W.ringCatSheaf) :=
  exists_fixedField_boundary_section_maps k R f ι n e a z g b ha M N hM hN eM eN
#print axioms AlgebraicGeometry.Scheme.CoherentGraph.exists_fixedField_boundary_section_maps
#print axioms AlgebraicGeometry.Scheme.CoherentGraph.exists_fixedField_boundary_section_pair
