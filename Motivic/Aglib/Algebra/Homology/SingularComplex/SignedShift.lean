/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Embedding.SignedShift
public import Motivic.Aglib.Algebra.Homology.Sheafification.Singular

/-!
# Signed shifts of ordinary singular cochains

The placement `r ↦ q-r` is naturally isomorphic to weight-zero singular
cochains shifted by `-q` using mathlib's actual signed shift functor. On chain
degree `r`, the comparison multiplies by `(-1)^(q*r)`. We specialize the
generic comparison to singular values, ordinary singular presheaves, and
canonical sheafification. In weight two all these signs are positive, and
the differential in degrees one and two is literally `face₀ - face₁`.

This is a convention bridge for ordinary singular cochains. It neither adds
transfers nor constructs the reduced transfer torus, and makes no claim that
these complexes are `Z(q)` or Bloch cycle complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SingularComplex

universe v u v' u'

variable {C : Type u} [Category.{v} C]
variable {A : Type u'} [Category.{v'} A]

section Values

variable [Preadditive A] [HasZeroObject A]

/-- The natural signed-shift comparison for singular values of presheaves. -/
def cochainShiftNatIso (Δ : CosimplicialObject C) (q : ℕ) :
    cochainFunctor (A := A) Δ q ≅
      cochainFunctor Δ 0 ⋙ CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-(q : ℤ)) :=
  isoWhiskerLeft (functor Δ) (_root_.HomologicalComplex.ExtensionSignedShift.naturalIso q)

/-- Actual singular cochains at weight `q` are weight zero shifted by `-q`. -/
def cochainShiftIso (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (q : ℕ) :
    cochainObj Δ P q ≅ (cochainObj Δ P 0)⟦-(q : ℤ)⟧ :=
  _root_.HomologicalComplex.ExtensionSignedShift.iso (obj Δ P) q

/-- Canonical identification of a shifted singular term with its presheaf value. -/
def shiftedCochainXIso (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (q r : ℕ) :
    ((cochainObj Δ P 0)⟦-(q : ℤ)⟧).X (Indexing.singularDegree q r) ≅
      P.obj (op (Δ.obj ⦋r⦌)) :=
  _root_.HomologicalComplex.ExtensionSignedShift.shiftedXIso (obj Δ P) q r rfl

/-- The exact sign of the singular comparison at every occupied term. -/
theorem cochainShiftIso_hom_f (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (q r : ℕ) :
    (cochainShiftIso Δ P q).hom.f (Indexing.singularDegree q r) =
      (-1 : ℤ) ^ (q * r) •
        ((cochainXIso Δ P q r).hom ≫ (shiftedCochainXIso Δ P q r).inv) := by
  change (_root_.HomologicalComplex.ExtensionSignedShift.iso (obj Δ P) q).hom.f ((q : ℤ) - r) =
    (-1 : ℤ) ^ (q * r) •
      (((obj Δ P).extendXIso (ComplexShape.embeddingUpIntLE (q : ℤ))
        (i' := (q : ℤ) - r) (ComplexShape.embeddingUpIntLE_f (q : ℤ) r)).hom ≫
        (_root_.HomologicalComplex.ExtensionSignedShift.shiftedXIso (obj Δ P) q r rfl).inv)
  simpa only [Units.smul_def, ← Nat.cast_mul, Int.coe_negOnePow_natCast] using
    _root_.HomologicalComplex.ExtensionSignedShift.iso_hom_f (obj Δ P) q r

/-- The signed comparison respects every differential, including zero terms. -/
theorem cochainShiftIso_comm (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A)
    (q : ℕ) (i j : ℤ) :
    (cochainShiftIso Δ P q).hom.f i ≫ ((cochainObj Δ P 0)⟦-(q : ℤ)⟧).d i j =
      (cochainObj Δ P q).d i j ≫ (cochainShiftIso Δ P q).hom.f j :=
  (cochainShiftIso Δ P q).hom.comm i j

/-- In weight two the comparison carries no component signs. -/
theorem cochainShiftIso_two_hom_f (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (r : ℕ) :
    (cochainShiftIso Δ P 2).hom.f (Indexing.singularDegree 2 r) =
      (cochainXIso Δ P 2 r).hom ≫ (shiftedCochainXIso Δ P 2 r).inv := by
  simp [cochainShiftIso_hom_f, pow_mul]

/-- The weight-two shifted differential is literally the alternating two-face map. -/
theorem shiftedWeightTwo_d_one_two (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    ((cochainObj Δ P 0)⟦(-2 : ℤ)⟧).d 1 2 =
      (shiftedCochainXIso Δ P 2 1).hom ≫
        (P.map (Δ.δ (0 : Fin 2)).op - P.map (Δ.δ (1 : Fin 2)).op) ≫
        (shiftedCochainXIso Δ P 2 0).inv := by
  have h := _root_.HomologicalComplex.ExtensionSignedShift.shifted_d (obj Δ P) 2 1 0
  change (((obj Δ P).extend (ComplexShape.embeddingUpIntLE 0))⟦(-2 : ℤ)⟧).d 1 2 =
    (-2 : ℤ).negOnePow •
      ((_root_.HomologicalComplex.ExtensionSignedShift.shiftedXIso (obj Δ P) 2 1 rfl).hom ≫
        (obj Δ P).d 1 0 ≫ (_root_.HomologicalComplex.ExtensionSignedShift.shiftedXIso (obj Δ P) 2 0
            rfl).inv) at h
  rw [show (-2 : ℤ).negOnePow = 1 by decide, one_smul, obj_d_one_zero] at h
  exact h

-- Normalize the definitionally equal degree and shift presentations when matching morphism types.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original weight-two differential agrees with the actual signed shift. -/
theorem weightTwo_d_matches_shift (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    (weightTwoXOneIso Δ P).inv ≫ (cochainObj Δ P 2).d 1 2 ≫
        (weightTwoXTwoIso Δ P).hom =
      (shiftedCochainXIso Δ P 2 1).inv ≫ ((cochainObj Δ P 0)⟦(-2 : ℤ)⟧).d 1 2 ≫
        (shiftedCochainXIso Δ P 2 0).hom := by
  rw [weightTwo_d_one_two, shiftedWeightTwo_d_one_two]
  simp

/-- The signed comparison is compatible with each map of presheaves. -/
theorem cochainShiftIso_naturality (Δ : CosimplicialObject C) {P Q : Cᵒᵖ ⥤ A}
    (α : P ⟶ Q) (q : ℕ) :
    cochainMap Δ α q ≫ (cochainShiftIso Δ Q q).hom =
      (cochainShiftIso Δ P q).hom ≫
        (CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-(q : ℤ))).map
          (cochainMap Δ α 0) :=
  (cochainShiftNatIso Δ q).hom.naturality α

end Values

section Sheaves

variable [HasBinaryProducts C] [Abelian A]
variable (J : GrothendieckTopology C) [HasSheafify J A]

/-- The signed comparison for the all-degree ordinary singular presheaf complex. -/
def presheafCochainShiftNatIso (Δ : CosimplicialObject C) (q : ℕ) :
    presheafCochainFunctor (A := A) Δ q ≅
      presheafCochainFunctor Δ 0 ⋙
        CategoryTheory.shiftFunctor (CochainComplex (Cᵒᵖ ⥤ A) ℤ) (-(q : ℤ)) :=
  isoWhiskerLeft (presheafConstruction (A := A) Δ)
    (_root_.HomologicalComplex.ExtensionSignedShift.naturalIso (A := Cᵒᵖ ⥤ A) q)

/-- The ordinary singular presheaf complex at weight `q` is a genuine signed shift. -/
def presheafCochainShiftIso (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (q : ℕ) :
    presheafCochainObj Δ P q ≅ (presheafCochainObj Δ P 0)⟦-(q : ℤ)⟧ :=
  (presheafCochainShiftNatIso Δ q).app P

/-- Canonical additive sheafification preserves the signed comparison naturally. -/
def sheafCochainShiftNatIso (Δ : CosimplicialObject C) (q : ℕ) :
    sheafCochainFunctor (A := A) J Δ q ≅
      sheafCochainFunctor J Δ 0 ⋙
        CategoryTheory.shiftFunctor (CochainComplex (Sheaf J A) ℤ) (-(q : ℤ)) :=
  isoWhiskerRight (presheafCochainShiftNatIso Δ q)
      (Sheafification.functor J (ComplexShape.up ℤ)) ≪≫
    isoWhiskerLeft (presheafCochainFunctor Δ 0)
      ((presheafToSheaf J A).mapCochainComplexShiftIso (-(q : ℤ)))

/-- Actual canonically sheafified ordinary singular cochains are signed shifts. -/
def sheafCochainShiftIso (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (q : ℕ) :
    sheafCochainObj J Δ P q ≅ (sheafCochainObj J Δ P 0)⟦-(q : ℤ)⟧ :=
  (sheafCochainShiftNatIso J Δ q).app P

/-- The sheafified comparison commutes with every presheaf map. -/
theorem sheafCochainShiftIso_naturality (Δ : CosimplicialObject C)
    {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (q : ℕ) :
    sheafCochainMap J Δ α q ≫ (sheafCochainShiftIso J Δ Q q).hom =
      (sheafCochainShiftIso J Δ P q).hom ≫
        (CategoryTheory.shiftFunctor (CochainComplex (Sheaf J A) ℤ) (-(q : ℤ))).map
          (sheafCochainMap J Δ α 0) :=
  (sheafCochainShiftNatIso J Δ q).hom.naturality α

end Sheaves

end CategoryTheory.SingularComplex
