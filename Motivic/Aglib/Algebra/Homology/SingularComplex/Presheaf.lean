/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.SingularComplex.Parameters

/-!
# Singular chains as a complex of presheaves

`CategoryTheory.SingularComplex.presheafObj Δ P` is an actual chain complex in the
presheaf category. Its degree-`n` presheaf sends `U` to `P(U × Δⁿ)`, with the
alternating face differential and the contravariant restriction maps already
constructed in `Parameters.lean`.

This form of the construction can subsequently be passed to an additive
sheafification functor. No topology, transfer structure, or sheafification is
assumed or constructed here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SingularComplex

universe v u v' u'

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable {A : Type u'} [Category.{v'} A] [Preadditive A]

/-- The all-degree singular chain complex in the category of ordinary presheaves. -/
noncomputable def presheafObj (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    ChainComplex (Cᵒᵖ ⥤ A) ℕ where
  X n := parameterFunctor Δ P ⋙ HomologicalComplex.eval A (ComplexShape.down ℕ) n
  d i j :=
    { app U := (parameterObj Δ P U.unop).d i j
      naturality _U _V f := (parameterMap Δ P f.unop).comm i j }
  shape i j hij := by
    ext U
    exact (parameterObj Δ P U.unop).shape i j hij
  d_comp_d' i j k _ _ := by
    ext U
    exact (parameterObj Δ P U.unop).d_comp_d i j k

@[simp]
theorem presheafObj_X_obj (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (n : ℕ) (U : Cᵒᵖ) :
    ((presheafObj Δ P).X n).obj U = P.obj (op (U.unop ⨯ Δ.obj ⦋n⦌)) :=
  rfl

@[simp]
theorem presheafObj_X_map (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (n : ℕ)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    ((presheafObj Δ P).X n).map f =
      P.map (prod.map f.unop (𝟙 (Δ.obj ⦋n⦌))).op :=
  rfl

/-- The presheaf differential evaluated at an object is the alternating geometric differential. -/
theorem presheafObj_d_app (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (n : ℕ) (U : Cᵒᵖ) :
    ((presheafObj Δ P).d (n + 1) n).app U =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        P.map (prod.map (𝟙 U.unop) (Δ.δ i)).op :=
  parameterObj_d Δ P U.unop n

/-- A presheaf map induces a chain map of presheaf-valued singular complexes. -/
noncomputable def presheafMap (Δ : CosimplicialObject C) {P Q : Cᵒᵖ ⥤ A}
    (α : P ⟶ Q) : presheafObj Δ P ⟶ presheafObj Δ Q where
  f n :=
    { app U := ((parameterNatTrans Δ α).app U).f n
      naturality _U _V f :=
        congrArg (fun g => g.f n) ((parameterNatTrans Δ α).naturality f) }
  comm' i j _ := by
    ext U
    exact ((parameterNatTrans Δ α).app U).comm i j

@[simp]
theorem presheafMap_f_app (Δ : CosimplicialObject C) {P Q : Cᵒᵖ ⥤ A}
    (α : P ⟶ Q) (n : ℕ) (U : Cᵒᵖ) :
    ((presheafMap Δ α).f n).app U = α.app (op (U.unop ⨯ Δ.obj ⦋n⦌)) :=
  rfl

/-- The singular chain construction as a functor from presheaves to their chain complexes. -/
noncomputable def presheafConstruction (Δ : CosimplicialObject C) :
    (Cᵒᵖ ⥤ A) ⥤ ChainComplex (Cᵒᵖ ⥤ A) ℕ where
  obj P := presheafObj Δ P
  map α := presheafMap Δ α
  map_id P := by
    ext n U
    rfl
  map_comp α β := by
    ext n U
    rfl

end CategoryTheory.SingularComplex
