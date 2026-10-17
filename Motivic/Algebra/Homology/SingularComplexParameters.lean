/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.SingularComplex
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-!
# Singular complexes with geometric parameters

In a category with binary products, `parameterObj Δ P U` has term
`P(U × Δⁿ)` in every chain degree. Its differential pulls back along the
maps `U × δᵢ`, with alternating signs. `parameterFunctor` packages the
contravariant dependence on `U`, including its identity and composition laws.
A map of presheaves gives a natural transformation of these complex-valued
presheaves.

Binary products here are categorical products in the chosen category. For
relative algebraic geometry one must choose the appropriate category over
the ground scheme; this module does not identify an absolute product with a
fiber product over a field.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open scoped Simplicial

namespace Motivic.SingularComplex

universe u v u' v'

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable {A : Type u'} [Category.{v'} A] [Preadditive A]

/-- The cosimplicial object `U × Δ`, using the products of the chosen category. -/
noncomputable def parameterCosimplicial (Δ : CosimplicialObject C) (U : C) :
    CosimplicialObject C :=
  Δ ⋙ prod.functor.obj U

/-- Singular chains evaluated with the geometric parameter `U`. -/
noncomputable def parameterObj (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (U : C) :
    ChainComplex A ℕ :=
  obj (parameterCosimplicial Δ U) P

@[simp]
theorem parameterObj_X (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (U : C) (n : ℕ) :
    (parameterObj Δ P U).X n = P.obj (op (U ⨯ Δ.obj ⦋n⦌)) :=
  rfl

/-- The differential is the alternating sum of pullbacks along `U × δᵢ`. -/
theorem parameterObj_d (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (U : C) (n : ℕ) :
    (parameterObj Δ P U).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        P.map (prod.map (𝟙 U) (Δ.δ i)).op :=
  obj_d (parameterCosimplicial Δ U) P n

/-- Pullback along a morphism of geometric parameters. -/
noncomputable def parameterMap (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A)
    {U V : C} (f : U ⟶ V) : parameterObj Δ P V ⟶ parameterObj Δ P U :=
  geometryMap (whiskerLeft Δ (prod.functor.map f)) P

@[simp]
theorem parameterMap_f (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A)
    {U V : C} (f : U ⟶ V) (n : ℕ) :
    (parameterMap Δ P f).f n = P.map (prod.map f (𝟙 (Δ.obj ⦋n⦌))).op :=
  rfl

@[simp]
theorem parameterMap_id (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (U : C) :
    parameterMap Δ P (𝟙 U) = 𝟙 (parameterObj Δ P U) := by
  ext n
  simp

@[simp]
theorem parameterMap_comp (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A)
    {U V W : C} (f : U ⟶ V) (g : V ⟶ W) :
    parameterMap Δ P (f ≫ g) = parameterMap Δ P g ≫ parameterMap Δ P f := by
  ext n
  simp only [HomologicalComplex.comp_f, parameterMap_f, prod.map_comp_id,
    op_comp, Functor.map_comp]
  rfl

/-- The complex-valued presheaf sending `U` to singular chains on `U × Δ`. -/
noncomputable def parameterFunctor (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    Cᵒᵖ ⥤ ChainComplex A ℕ where
  obj U := parameterObj Δ P U.unop
  map f := parameterMap Δ P f.unop
  map_id U := by simp
  map_comp f g := by simp

/-- A presheaf morphism induces a morphism of parameterized complex-valued presheaves. -/
noncomputable def parameterNatTrans (Δ : CosimplicialObject C)
    {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) :
    parameterFunctor Δ P ⟶ parameterFunctor Δ Q where
  app U := map (parameterCosimplicial Δ U.unop) α
  naturality _U _V f :=
    geometryMap_naturality (whiskerLeft Δ (prod.functor.map f.unop)) α

@[simp]
theorem parameterNatTrans_app_f (Δ : CosimplicialObject C)
    {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (U : Cᵒᵖ) (n : ℕ) :
    ((parameterNatTrans Δ α).app U).f n = α.app (op (U.unop ⨯ Δ.obj ⦋n⦌)) :=
  rfl

/-- The parameterized singular construction is functorial in the original presheaf. -/
noncomputable def parameterConstruction (Δ : CosimplicialObject C) :
    (Cᵒᵖ ⥤ A) ⥤ Cᵒᵖ ⥤ ChainComplex A ℕ where
  obj P := parameterFunctor Δ P
  map α := parameterNatTrans Δ α
  map_id P := by
    ext U n
    rfl
  map_comp α β := by
    ext U n
    rfl

end Motivic.SingularComplex
