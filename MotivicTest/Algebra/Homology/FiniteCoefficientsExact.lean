/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Motivic.Algebra.Homology.FiniteCoefficientsExact

/-!
# Exact coefficient sequence regression tests

These consumers use actual cohomology objects and canonical coefficient maps.
They check composite level six, degree one to degree two, the integral-modulo
kernel, surjectivity onto torsion, and level-one vanishing without prime-level
or Bockstein-injectivity assumptions.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open Motivic Motivic.finiteCoefficients

set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u

variable (K : CochainComplex (ModuleCat.{u} ℤ) ℤ)

/-- The coefficient short exact sequence works at the composite level six. -/
example : (moduleCohomologyShortComplex K 6 1).ShortExact :=
  moduleCohomologyShortComplex_shortExact K 6 1

/-- At level six, the actual degree-one Bockstein has exactly the integral-image kernel. -/
example (x : (finiteCoefficients K 6).homology 1) :
    bocksteinHomology K 6 1 x = 0 ↔
      ∃ y : K.homology 1, integralHomology K 6 1 y = x :=
  bocksteinHomology_eq_zero_iff K 6 1 x

/-- Every degree-two class killed by six is the positive Bockstein of a finite class. -/
example (y : K.homology 2) (hy : 6 • y = 0) :
    ∃ x : (finiteCoefficients K 6).homology 1, bocksteinHomology K 6 1 x = y :=
  exists_bocksteinHomology_eq K 6 1 y hy

/-- The canonical map from integral cohomology modulo six is injective. -/
example : Function.Injective (integralModulo K 6 1) :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

/-- The positive Bockstein is surjective onto the concrete six-torsion submodule. -/
example : Function.Surjective (bocksteinNTorsion K 6 1) :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- The torsion-valued Bockstein has exactly the integral-modulo kernel. -/
example (x : (finiteCoefficients K 6).homology 1) :
    bocksteinNTorsion K 6 1 x = 0 ↔
      ∃ y : K.homology 1 ⧸ LinearMap.range (6 • 𝟙 (K.homology 1)).hom,
        integralModulo K 6 1 y = x :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (moduleCohomologyShortComplex_shortExact K 6 1).exact x

/-- Level one participates in the same canonical short exact sequence. -/
example (i : ℤ) : (cohomologyShortComplex K 1 i).ShortExact :=
  cohomologyShortComplex_shortExact K 1 i

/-- Level-one finite cohomology still vanishes in every degree. -/
example (i : ℤ) : IsZero ((finiteCoefficients K 1).homology i) :=
  isZero_homology_one K i

/-- Reduction annihilation uses the scalar simp-normal form automatically. -/
example : (6 • 𝟙 (K.homology 1)) ≫ integralHomology K 6 1 = 0 := by
  simp

/-- The reassociated reduction equation is still available to simplification. -/
example {X : ModuleCat.{u} ℤ} (f : (finiteCoefficients K 6).homology 1 ⟶ X) :
    (6 • 𝟙 (K.homology 1)) ≫ integralHomology K 6 1 ≫ f = 0 := by
  simp

/-- Bockstein annihilation uses the scalar simp-normal form automatically. -/
example (i : ℤ) : bocksteinHomology K 6 i ≫ (6 • 𝟙 (K.homology (i + 1))) = 0 := by
  simp

/-- The reassociated Bockstein equation is still available to simplification. -/
example (i : ℤ) {X : ModuleCat.{u} ℤ} (f : K.homology (i + 1) ⟶ X) :
    bocksteinHomology K 6 i ≫ (6 • 𝟙 (K.homology (i + 1))) ≫ f = 0 := by
  simp

section NormalizedModuleMaps

variable {R : Type u} [Ring R] (M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) (i : ℤ)

/-- Quotient reduction simplifies even when written using categorical multiplication. -/
example : ModuleCat.ofHom (LinearMap.range (n • 𝟙 (M.homology i)).hom).mkQ ≫
    integralModulo M n i = integralHomology M n i := by
  simp

/-- The concrete torsion inclusion simplifies to the positive Bockstein. -/
example : bocksteinNTorsion M n i ≫
    ModuleCat.ofHom (LinearMap.ker (n • 𝟙 (M.homology (i + 1))).hom).subtype =
      bocksteinHomology M n i := by
  simp

end NormalizedModuleMaps
