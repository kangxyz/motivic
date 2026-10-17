/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.SheafificationSingular
public import Motivic.Algebra.Homology.FiniteCoefficientsCohomology
public import Motivic.AlgebraicGeometry.AlgebraicSimplexScheme
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Consumers of sheafified ordinary singular cochains

The generic checks exercise the degree-two weight dictionary and the canonical
unit. An additional consumer uses the actual relative algebraic simplex over
`Spec R`. On the trivial topology its sheafification instance is supplied
without hypotheses, and its all-degree homology comparison is constructed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic.SingularComplex Motivic.AlgebraicSimplex

universe v u w

section Generic

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]
variable (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})

example : (sheafCochainObj J Δ P 2).X 1 ≅
    (presheafToSheaf J AddCommGrpCat.{w}).obj ((presheafObj Δ P).X 1) :=
  sheafWeightTwoXOneIso J Δ P

example : (sheafCochainObj J Δ P 2).X 2 ≅
    (presheafToSheaf J AddCommGrpCat.{w}).obj ((presheafObj Δ P).X 0) :=
  sheafWeightTwoXTwoIso J Δ P

example : IsZero ((sheafCochainObj J Δ P 2).X 3) :=
  isZero_sheafCochainObj_X J Δ P 2 3 (by decide)

example (q r : ℕ) :
    (sheafCochainObj J Δ P q).homology (Motivic.Indexing.singularDegree q r) ≅
      (presheafToSheaf J AddCommGrpCat.{w}).obj ((presheafObj Δ P).homology r) :=
  sheafCochainHomologyIso J Δ P q r

example {Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (α : P ⟶ Q) (q : ℕ) :
    (presheafCochainFunctor Δ q).map α ≫ (sheafCochainUnit J Δ q).app Q =
      (sheafCochainUnit J Δ q).app P ≫
        (Motivic.Sheafification.underlyingFunctor J (ComplexShape.up ℤ)).map
          (sheafCochainMap J Δ α q) :=
  (sheafCochainUnit J Δ q).naturality α

example (i : ℤ) :
    IsZero ((Motivic.finiteCoefficients (sheafCochainObj J Δ P 2) 1).homology i) :=
  Motivic.finiteCoefficients.isZero_homology_one (sheafCochainObj J Δ P 2) i

example :
    (Motivic.finiteCoefficients (sheafCochainObj J Δ P 2) 6).homology 1 ⟶
      (sheafCochainObj J Δ P 2).homology 2 :=
  Motivic.finiteCoefficients.bocksteinHomology (sheafCochainObj J Δ P 2) 6 1

/-- Functorial identities simplify without duplicate specialized simp lemmas. -/
example (q : ℕ) : sheafCochainMap J Δ (𝟙 P) q = 𝟙 (sheafCochainObj J Δ P q) := by
  simp

/-- Composition also uses the general functor simp rule. -/
example {Q S : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (α : P ⟶ Q) (β : Q ⟶ S) (q : ℕ) :
    sheafCochainMap J Δ (α ≫ β) q =
      sheafCochainMap J Δ α q ≫ sheafCochainMap J Δ β q := by
  simp

end Generic

section RelativeSimplex

variable (R : Type u) [CommRing R]
variable (P : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ AddCommGrpCat.{w})

/-- A hypothesis-free sheafification consumer on the actual relative algebraic simplex. -/
def ordinaryWeightTwo :
    CochainComplex (Sheaf (⊥ : GrothendieckTopology (Over (Spec (CommRingCat.of R))))
      AddCommGrpCat.{w}) ℤ :=
  sheafCochainObj ⊥ (cosimplicialSchemeOver R) P 2

example : (ordinaryWeightTwo R P).homology 1 ≅
    (presheafToSheaf (⊥ : GrothendieckTopology (Over (Spec (CommRingCat.of R))))
      AddCommGrpCat.{w}).obj ((presheafObj (cosimplicialSchemeOver R) P).homology 1) :=
  sheafCochainHomologyIso ⊥ (cosimplicialSchemeOver R) P 2 1

example (i j k : ℤ) :
    (ordinaryWeightTwo R P).d i j ≫ (ordinaryWeightTwo R P).d j k = 0 :=
  (ordinaryWeightTwo R P).d_comp_d i j k

end RelativeSimplex

set_option linter.hashCommand false in
#print axioms Motivic.SingularComplex.sheafCochainObj
set_option linter.hashCommand false in
#print axioms Motivic.SingularComplex.sheafCochainObj_d
set_option linter.hashCommand false in
#print axioms Motivic.SingularComplex.sheafCochainHomologyIso
