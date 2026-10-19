/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.SingularComplex.SignedShift
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Consumers of the singular signed-shift comparison

These checks exercise the genuine natural isomorphisms, their differential and
map compatibility, an odd-weight negative component, and the literal two-face
weight-two differential. Canonical sheafification is tested over the trivial
topology with no assumed comparison isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.CategoryTheory.SingularComplex
open scoped Simplicial

universe v u w

variable {C : Type u} [Category.{v} C]
variable (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})

example (q : ℕ) : cochainObj Δ P q ≅ (cochainObj Δ P 0)⟦-(q : ℤ)⟧ :=
  cochainShiftIso Δ P q

example (q r : ℕ) :
    (cochainShiftIso Δ P q).hom.f (Indexing.singularDegree q r) =
      (-1 : ℤ) ^ (q * r) •
        ((cochainXIso Δ P q r).hom ≫ (shiftedCochainXIso Δ P q r).inv) :=
  cochainShiftIso_hom_f Δ P q r

/-- Weight one has a negative chain-one comparison component. -/
example : (cochainShiftIso Δ P 1).hom.f 0 =
    (-1 : ℤ) • ((cochainXIso Δ P 1 1).hom ≫ (shiftedCochainXIso Δ P 1 1).inv) := by
  change (cochainShiftIso Δ P 1).hom.f (Indexing.singularDegree 1 1) =
    (-1 : ℤ) • ((cochainXIso Δ P 1 1).hom ≫ (shiftedCochainXIso Δ P 1 1).inv)
  simpa only [Nat.one_mul, pow_one] using cochainShiftIso_hom_f Δ P 1 1

example (q : ℕ) (i j : ℤ) :
    (cochainShiftIso Δ P q).hom.f i ≫ ((cochainObj Δ P 0)⟦-(q : ℤ)⟧).d i j =
      (cochainObj Δ P q).d i j ≫ (cochainShiftIso Δ P q).hom.f j :=
  cochainShiftIso_comm Δ P q i j

example {Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (α : P ⟶ Q) (q : ℕ) :
    cochainMap Δ α q ≫ (cochainShiftIso Δ Q q).hom =
      (cochainShiftIso Δ P q).hom ≫
        (shiftFunctor (CochainComplex AddCommGrpCat.{w} ℤ) (-(q : ℤ))).map
          (cochainMap Δ α 0) :=
  cochainShiftIso_naturality Δ α q

example : ((cochainObj Δ P 0)⟦(-2 : ℤ)⟧).d 1 2 =
    (shiftedCochainXIso Δ P 2 1).hom ≫
      (P.map (Δ.δ (0 : Fin 2)).op - P.map (Δ.δ (1 : Fin 2)).op) ≫
        (shiftedCochainXIso Δ P 2 0).inv :=
  shiftedWeightTwo_d_one_two Δ P

example : (cochainShiftIso Δ P 2).hom.f 1 =
    (weightTwoXOneIso Δ P).hom ≫ (shiftedCochainXIso Δ P 2 1).inv :=
  cochainShiftIso_two_hom_f Δ P 1

example : (cochainShiftIso Δ P 2).hom.f 2 =
    (weightTwoXTwoIso Δ P).hom ≫ (shiftedCochainXIso Δ P 2 0).inv :=
  cochainShiftIso_two_hom_f Δ P 0

section Sheaves

variable [HasBinaryProducts C]

example (q : ℕ) : presheafCochainObj Δ P q ≅ (presheafCochainObj Δ P 0)⟦-(q : ℤ)⟧ :=
  presheafCochainShiftIso Δ P q

example (q : ℕ) :
    sheafCochainObj (⊥ : GrothendieckTopology C) Δ P q ≅
      (sheafCochainObj ⊥ Δ P 0)⟦-(q : ℤ)⟧ :=
  sheafCochainShiftIso ⊥ Δ P q

example {Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (α : P ⟶ Q) (q : ℕ) :
    sheafCochainMap (⊥ : GrothendieckTopology C) Δ α q ≫
        (sheafCochainShiftIso ⊥ Δ Q q).hom =
      (sheafCochainShiftIso ⊥ Δ P q).hom ≫
        (shiftFunctor (CochainComplex (Sheaf (⊥ : GrothendieckTopology C)
          AddCommGrpCat.{w}) ℤ) (-(q : ℤ))).map (sheafCochainMap ⊥ Δ α 0) :=
  sheafCochainShiftIso_naturality ⊥ Δ α q

end Sheaves
