/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FirstQuadrantAcyclic
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Tensoring an acyclic nonnegative complex with a flat complex

Degreewise flatness makes each horizontal tensor row exact. The finite
first-quadrant staircase theorem then proves acyclicity of the actual signed
tensor total, even when both factors are unbounded above. A projective
resolution supplies the flat terms in the intended Tor application. No
flatness or projectivity of the module being resolved is assumed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex

universe u

namespace ModuleCat.TorComparison

variable {R : Type u} [CommRing R]

/-- An acyclic complex stays acyclic after tensoring with a degreewise flat
nonnegative complex and taking the actual signed total. -/
theorem flatComplexTensor_acyclic
    (A G : ChainComplex (ModuleCat.{u} R) ℕ) (hA : A.Acyclic)
    [∀ q, Module.Flat R (G.X q)] :
    (mapBifunctor A G (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)).Acyclic := by
  apply firstQuadrant_total_acyclic
  intro q p
  change ((A.sc p).map (tensorRight (G.X q))).Exact
  exact Module.Flat.rTensor_shortComplex_exact (G.X q) (A.sc p) (hA p)

/-- In particular, the second factor can be any genuine projective resolution. -/
theorem resolutionTensor_acyclic
    (A : ChainComplex (ModuleCat.{u} R) ℕ) (hA : A.Acyclic)
    {N : ModuleCat.{u} R} (G : ProjectiveResolution N) :
    (mapBifunctor A G.complex (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)).Acyclic :=
  flatComplexTensor_acyclic A G.complex hA

end ModuleCat.TorComparison
