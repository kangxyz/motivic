/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.SingularComplex.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Singular and higher-Chow degree conventions

`CategoryTheory.SingularComplex.Indexing.singularDegree q r` places singular chain degree `r` in
cochain
degree `q - r`. `CategoryTheory.SingularComplex.cochainObj` realizes this placement as
an actual integer-indexed cochain complex, extended by zero above weight `q`.
Its differential is the original alternating-face differential, transported
through the specified term isomorphisms. This file supplies explicit degree placement. The separate
comparison with
Mathlib's signed shift functor is constructed in `SignedShift.lean`, including
the factor `(-1)^(q*r)` in chain degree `r`.

For comparison only, Bloch's convention uses chain degree `2q - i` in cochain
degree `i`. In weight two, cochain degrees one and two therefore use singular
chain degrees one and zero, but Bloch chain degrees three and two. The numerical
dictionary is not a comparison theorem between those complexes.
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits
open scoped Simplicial

namespace CategoryTheory.SingularComplex.Indexing

/-- Cochain degree of singular chain degree `r` at weight `q`. -/
def singularDegree (q r : ℕ) : ℤ := (q : ℤ) - (r : ℤ)

/-- Bloch chain index corresponding to cochain degree `i` at weight `q`. -/
def blochDegree (q : ℕ) (i : ℤ) : ℤ := 2 * (q : ℤ) - i

@[simp]
theorem singularDegree_zero (q : ℕ) : singularDegree q 0 = q := by
  simp [singularDegree]

/-- A descending singular differential raises cochain degree by one. -/
theorem singularDegree_succ (q r : ℕ) :
    singularDegree q (r + 1) + 1 = singularDegree q r := by
  simp only [singularDegree, Nat.cast_add, Nat.cast_one]
  omega

/-- Under the two conventions, the same cochain degree has Bloch index `q + r`. -/
theorem blochDegree_singularDegree (q r : ℕ) :
    blochDegree q (singularDegree q r) = (q : ℤ) + (r : ℤ) := by
  simp [blochDegree, singularDegree]
  omega

@[simp]
theorem singularDegree_two_zero : singularDegree 2 0 = 2 := rfl

@[simp]
theorem singularDegree_two_one : singularDegree 2 1 = 1 := rfl

@[simp]
theorem blochDegree_two_one : blochDegree 2 1 = 3 := rfl

@[simp]
theorem blochDegree_two_two : blochDegree 2 2 = 2 := rfl

end CategoryTheory.SingularComplex.Indexing

namespace CategoryTheory.SingularComplex

universe u v u' v'

variable {C : Type u} [Category.{v} C]
variable {A : Type u'} [Category.{v'} A] [Preadditive A] [HasZeroObject A]

/-- Singular complexes placed in cochain degree `q - r`, functorially in the presheaf. -/
noncomputable def cochainFunctor (Δ : CosimplicialObject C) (q : ℕ) :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℤ :=
  functor Δ ⋙ (ComplexShape.embeddingUpIntLE (q : ℤ)).extendFunctor A

/-- The actual cochain complex with singular chain term `r` in degree `q - r`. -/
noncomputable def cochainObj (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (q : ℕ) :
    CochainComplex A ℤ :=
  (cochainFunctor Δ q).obj P

/-- The canonical identification of a placed cochain term with its presheaf value. -/
noncomputable def cochainXIso (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (q r : ℕ) :
    (cochainObj Δ P q).X (Indexing.singularDegree q r) ≅ P.obj (op (Δ.obj ⦋r⦌)) :=
  (obj Δ P).extendXIso (ComplexShape.embeddingUpIntLE (q : ℤ)) rfl

/-- The placed complex is zero in every cochain degree above the weight. -/
theorem isZero_cochainObj_X (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A)
    (q : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero ((cochainObj Δ P q).X i) := by
  apply (obj Δ P).isZero_extend_X
  exact (ComplexShape.notMem_range_embeddingUpIntLE_iff (q : ℤ) i).2 hi

/-- The degree placement preserves the differential, without an implicit sign change. -/
theorem cochainObj_d (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (q r : ℕ) :
    (cochainObj Δ P q).d (Indexing.singularDegree q (r + 1))
        (Indexing.singularDegree q r) =
      (cochainXIso Δ P q (r + 1)).hom ≫ (obj Δ P).d (r + 1) r ≫
        (cochainXIso Δ P q r).inv :=
  (obj Δ P).extend_d_eq (ComplexShape.embeddingUpIntLE (q : ℤ)) rfl rfl

/-- Differential square-zero for the integer-indexed complex in every degree. -/
theorem cochainObj_d_squared (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A)
    (q : ℕ) (i j k : ℤ) :
    (cochainObj Δ P q).d i j ≫ (cochainObj Δ P q).d j k = 0 :=
  (cochainObj Δ P q).d_comp_d i j k

/-- A map of presheaves induces a map after the cochain placement. -/
noncomputable def cochainMap (Δ : CosimplicialObject C) {P Q : Cᵒᵖ ⥤ A}
    (α : P ⟶ Q) (q : ℕ) : cochainObj Δ P q ⟶ cochainObj Δ Q q :=
  (cochainFunctor Δ q).map α

@[simp]
theorem cochainMap_id (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (q : ℕ) :
    cochainMap Δ (𝟙 P) q = 𝟙 (cochainObj Δ P q) :=
  (cochainFunctor Δ q).map_id P

@[simp]
theorem cochainMap_comp (Δ : CosimplicialObject C) {P Q R : Cᵒᵖ ⥤ A}
    (α : P ⟶ Q) (β : Q ⟶ R) (q : ℕ) :
    cochainMap Δ (α ≫ β) q = cochainMap Δ α q ≫ cochainMap Δ β q :=
  (cochainFunctor Δ q).map_comp α β

/-- The placed presheaf map has its original component under the canonical term isomorphisms. -/
theorem cochainMap_f (Δ : CosimplicialObject C) {P Q : Cᵒᵖ ⥤ A}
    (α : P ⟶ Q) (q r : ℕ) :
    (cochainMap Δ α q).f (Indexing.singularDegree q r) =
      (cochainXIso Δ P q r).hom ≫ α.app (op (Δ.obj ⦋r⦌)) ≫
        (cochainXIso Δ Q q r).inv :=
  HomologicalComplex.extendMap_f (map Δ α) (ComplexShape.embeddingUpIntLE (q : ℤ)) rfl

/-- At weight two, cochain degree one is the singular chain-one presheaf value. -/
noncomputable def weightTwoXOneIso (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    (cochainObj Δ P 2).X 1 ≅ P.obj (op (Δ.obj ⦋1⦌)) :=
  cochainXIso Δ P 2 1

/-- At weight two, cochain degree two is the singular chain-zero presheaf value. -/
noncomputable def weightTwoXTwoIso (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    (cochainObj Δ P 2).X 2 ≅ P.obj (op (Δ.obj ⦋0⦌)) :=
  cochainXIso Δ P 2 0

/-- The exact weight-two differential from cochain degree one to two. -/
theorem weightTwo_d_one_two (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    (cochainObj Δ P 2).d 1 2 =
      (weightTwoXOneIso Δ P).hom ≫
        (P.map (Δ.δ (0 : Fin 2)).op - P.map (Δ.δ (1 : Fin 2)).op) ≫
        (weightTwoXTwoIso Δ P).inv := by
  simpa [weightTwoXOneIso, weightTwoXTwoIso, obj_d_one_zero] using cochainObj_d Δ P 2 0

end CategoryTheory.SingularComplex
