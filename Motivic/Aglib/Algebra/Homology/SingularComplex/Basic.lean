/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# The singular complex of a presheaf

For a cosimplicial object `Δ` of a category `C` and a presheaf `P` with values in a
preadditive category, `CategoryTheory.SingularComplex.obj Δ P` is the actual unbounded
nonnegative chain complex with term `P(Δⁿ)` and alternating face differential.
The construction is covariant in the presheaf and contravariant in `Δ`.
In particular it applies to presheaves of abelian groups.

This construction does not supply transfers, sheafification, a reduced torus, or
an identification with a motivic complex. Those are separate geometric inputs.

## References

* Mazza, Voevodsky, Weibel, *Lecture Notes on Motivic Cohomology*, Definition 3.1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite AlgebraicTopology
open scoped Simplicial

namespace CategoryTheory.SingularComplex

universe u v u' v'

variable {C : Type u} [Category.{v} C]
variable {A : Type u'} [Category.{v'} A]

/-- The simplicial object obtained by evaluating a presheaf on a cosimplicial object. -/
def simplicial (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) : SimplicialObject A :=
  Δ.op ⋙ P

@[simp]
theorem simplicial_obj (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (simplicial Δ P).obj (op ⦋n⦌) = P.obj (op (Δ.obj ⦋n⦌)) :=
  rfl

@[simp]
theorem simplicial_δ (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A)
    {n : ℕ} (i : Fin (n + 2)) :
    (simplicial Δ P).δ i = P.map (Δ.δ i).op :=
  rfl

@[simp]
theorem simplicial_σ (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A)
    {n : ℕ} (i : Fin (n + 1)) :
    (simplicial Δ P).σ i = P.map (Δ.σ i).op :=
  rfl

variable [Preadditive A]

/-- The singular chain construction as a functor of presheaves. -/
def functor (Δ : CosimplicialObject C) : (Cᵒᵖ ⥤ A) ⥤ ChainComplex A ℕ :=
  (whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ A).obj Δ.op ⋙ alternatingFaceMapComplex A

/-- The all-degree singular chain complex of a presheaf on a cosimplicial object. -/
def obj (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) : ChainComplex A ℕ :=
  (functor Δ).obj P

@[simp]
theorem obj_X (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (obj Δ P).X n = P.obj (op (Δ.obj ⦋n⦌)) :=
  rfl

/-- Every differential is the alternating sum of the geometric coface pullbacks. -/
theorem obj_d (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (obj Δ P).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • P.map (Δ.δ i).op := by
  exact AlternatingFaceMapComplex.obj_d_eq (simplicial Δ P) n

/-- The singular differential squares to zero in every degree. -/
theorem d_squared (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (obj Δ P).d (n + 2) (n + 1) ≫ (obj Δ P).d (n + 1) n = 0 :=
  (obj Δ P).d_comp_d _ _ _

/-- The differential from chain degree one to zero, with its signs fixed. -/
theorem obj_d_one_zero (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    (obj Δ P).d 1 0 = P.map (Δ.δ (0 : Fin 2)).op - P.map (Δ.δ (1 : Fin 2)).op := by
  rw [obj_d]
  simp [Fin.sum_univ_two, sub_eq_add_neg]

/-- A natural transformation of presheaves induces a chain map. -/
def map (Δ : CosimplicialObject C) {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) :
    obj Δ P ⟶ obj Δ Q :=
  (functor Δ).map α

@[simp]
theorem map_f (Δ : CosimplicialObject C) {P Q : Cᵒᵖ ⥤ A}
    (α : P ⟶ Q) (n : ℕ) :
    (map Δ α).f n = α.app (op (Δ.obj ⦋n⦌)) :=
  rfl

@[simp]
theorem map_id (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    map Δ (𝟙 P) = 𝟙 (obj Δ P) :=
  (functor Δ).map_id P

@[simp]
theorem map_comp (Δ : CosimplicialObject C) {P Q R : Cᵒᵖ ⥤ A}
    (α : P ⟶ Q) (β : Q ⟶ R) :
    map Δ (α ≫ β) = map Δ α ≫ map Δ β :=
  (functor Δ).map_comp α β

/-- A map of cosimplicial geometric objects induces a chain map in the reverse direction. -/
def geometryMap {Δ Γ : CosimplicialObject C} (f : Δ ⟶ Γ) (P : Cᵒᵖ ⥤ A) :
    obj Γ P ⟶ obj Δ P :=
  (alternatingFaceMapComplex A).map (whiskerRight (NatTrans.op f) P)

@[simp]
theorem geometryMap_f {Δ Γ : CosimplicialObject C} (f : Δ ⟶ Γ)
    (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (geometryMap f P).f n = P.map (f.app ⦋n⦌).op :=
  rfl

@[simp]
theorem geometryMap_id (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    geometryMap (𝟙 Δ) P = 𝟙 (obj Δ P) := by
  ext n
  simp

@[simp]
theorem geometryMap_comp {Δ Γ Θ : CosimplicialObject C} (f : Δ ⟶ Γ) (g : Γ ⟶ Θ)
    (P : Cᵒᵖ ⥤ A) :
    geometryMap (f ≫ g) P = geometryMap g P ≫ geometryMap f P := by
  ext n
  simp

/-- Presheaf maps commute with contravariant maps of the geometric input. -/
theorem geometryMap_naturality {Δ Γ : CosimplicialObject C} (f : Δ ⟶ Γ)
    {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) :
    geometryMap f P ≫ map Δ α = map Γ α ≫ geometryMap f Q := by
  ext n
  exact α.naturality (f.app ⦋n⦌).op

end CategoryTheory.SingularComplex
