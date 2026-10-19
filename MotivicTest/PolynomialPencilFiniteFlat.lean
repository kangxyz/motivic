/-
Copyright (c) 2026 Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.Polynomial.FiniteFlat

/-! # Literal polynomial family finite-flat consumer and axiom audit -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open PolynomialBoundaryPencil
universe u
variable {R : Type u} [CommRing R]

example {S C D B : Scheme.{u}} (bS : S ⟶ Spec (.of R))
    [IsAffine S] (q : C ⟶ S) [IsProper q]
    (j : D ⟶ C) [IsOpenImmersion j] [D.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)] (i : B ⟶ C)
    (L : LineBundle C) (a c : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    [IsIso ((Scheme.Modules.pullback i).map a)]
    (h : Hom.pullbackToUnit a i = Hom.pullbackToUnit c i)
    (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range i) :
    let f := familyMap ((j ≫ q) ≫ bS) (pullbackLineBundle j L)
      (Hom.pullbackToUnit a j) (Hom.pullbackToUnit c j)
    IsFinite (Hom.zeroInclusion f ≫ parameterMap bS (j ≫ q)) ∧
      Flat (Hom.zeroInclusion f ≫ parameterMap bS (j ≫ q)) :=
  retained_familySource_finite_flat bS q j i L a c h hcover

open Lean in
run_cmd do
  for name in #[``retained_familySource_finite_flat, ``restrictionZeroIso,
      ``parameterMap_comp] do
    for axiomName in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "{name} depends on unsupported assumption {axiomName}"
  logInfo "Literal polynomial family finiteness and flatness use only standard Lean foundations."
