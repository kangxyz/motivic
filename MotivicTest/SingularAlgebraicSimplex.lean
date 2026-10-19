/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Motivic.Aglib.AlgebraicGeometry.Simplex.AlgebraicSimplexScheme
import Motivic.Aglib.Algebra.Homology.SingularComplex.Presheaf
import Motivic.Aglib.Algebra.Homology.SingularComplex.Normalization
import Motivic.Aglib.Algebra.Homology.SingularComplex.Indexing
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Singular chains on the actual relative algebraic simplex

The geometric input is the quotient-ring algebraic simplex, viewed as a
cosimplicial scheme over `Spec R`. The parameters use products in that over
category, hence are relative to `Spec R`. The consumers below exercise the
actual all-degree complex of presheaves, the weight-two differential, and
the actual Moore normalization inclusion for this geometric input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open _root_.AlgebraicSimplex _root_.CategoryTheory.SingularComplex
open scoped Simplicial

universe u w

variable (R : Type u) [CommRing R]

variable (P : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ AddCommGrpCat.{w})

example (n : ℕ) (U : Over (Spec (CommRingCat.of R))) :
    ((presheafObj (cosimplicialSchemeOver R) P).X n).obj (op U) =
      P.obj (op (U ⨯ Over.mk (structureMap R n))) :=
  rfl

example (n : ℕ) (U : Over (Spec (CommRingCat.of R))) :
    (parameterObj (cosimplicialSchemeOver R) P U).d (n + 2) (n + 1) ≫
      (parameterObj (cosimplicialSchemeOver R) P U).d (n + 1) n = 0 :=
  (parameterObj (cosimplicialSchemeOver R) P U).d_comp_d _ _ _

example (U : Over (Spec (CommRingCat.of R))) :
    (cochainObj (parameterCosimplicial (cosimplicialSchemeOver R) U) P 2).X 1 ≅
      P.obj (op (U ⨯ Over.mk (structureMap R 1))) :=
  weightTwoXOneIso (parameterCosimplicial (cosimplicialSchemeOver R) U) P

example (U : Over (Spec (CommRingCat.of R))) :
    (cochainObj (parameterCosimplicial (cosimplicialSchemeOver R) U) P 2).X 2 ≅
      P.obj (op (U ⨯ Over.mk (structureMap R 0))) :=
  weightTwoXTwoIso (parameterCosimplicial (cosimplicialSchemeOver R) U) P

example (U : Over (Spec (CommRingCat.of R))) :
    QuasiIso ((normalizedInclusion
      (parameterCosimplicial (cosimplicialSchemeOver R) U)).app P) :=
  inferInstance
