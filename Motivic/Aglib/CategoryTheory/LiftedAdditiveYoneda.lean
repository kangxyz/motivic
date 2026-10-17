/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.AdditiveFunctorAB5
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Generator.Basic

/-!
# Lifted additive representables and a separator

Additive Yoneda with coefficients in the universe of both source objects and
source morphisms. The coproduct of these actual lifted representables is a
separator for additive abelian-group-valued presheaves.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace CategoryTheory.AdditiveFunctor

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The additive representable with its groups lifted to the source object universe. -/
def liftedRepresentable (X : C) : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v} := by
  letI : AddCommGrpCat.uliftFunctor.{u, v}.Additive := ⟨by intros; rfl⟩
  exact .of ((preadditiveYoneda.obj X) ⋙ AddCommGrpCat.uliftFunctor.{u})

/-- A section defines a morphism from the actual lifted additive representable. -/
def liftedSectionHom (P : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v}) (X : C)
    (s : P.obj.obj (op X)) : liftedRepresentable X ⟶ P :=
  ObjectProperty.homMk
    { app Y := by
        change AddCommGrpCat.of (ULift.{u} (Y.unop ⟶ X)) ⟶ P.obj.obj Y
        exact AddCommGrpCat.ofHom
         { toFun α := P.obj.map α.down.op s
           map_zero' := by
            change P.obj.map (0 : Y.unop ⟶ X).op s = 0
            rw [op_zero, P.obj.map_zero]
            rfl
           map_add' α β := by
            change P.obj.map (α.down + β.down).op s = _
            rw [op_add, P.obj.map_add]
            rfl }
      naturality Y Z f := by
        ext α
        change ULift.{u} (Y.unop ⟶ X) at α
        change P.obj.map (f.unop ≫ α.down).op s =
          P.obj.map f (P.obj.map α.down.op s)
        rw [op_comp, P.obj.map_comp]
        rfl }

/-- Additive Yoneda for the lifted representable. -/
def liftedYonedaAddEquiv (P : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v}) (X : C) :
    (liftedRepresentable X ⟶ P) ≃+ P.obj.obj (op X) where
  toFun η := η.hom.app (op X) (ULift.up (𝟙 X))
  invFun := liftedSectionHom P X
  left_inv η := by
    apply ObjectProperty.hom_ext
    ext Y α
    change ULift.{u} (Y.unop ⟶ X) at α
    change P.obj.map α.down.op (η.hom.app (op X) (ULift.up (𝟙 X))) =
      η.hom.app Y α
    have h := ConcreteCategory.congr_hom (η.hom.naturality α.down.op)
      (ULift.up (𝟙 X))
    change η.hom.app Y (ULift.up (α.down ≫ 𝟙 X)) =
      P.obj.map α.down.op (η.hom.app (op X) (ULift.up (𝟙 X))) at h
    rw [Category.comp_id] at h
    exact h.symm
  right_inv s := by
    change P.obj.map (𝟙 X).op s = s
    rw [op_id, P.obj.map_id]
    rfl
  map_add' _ _ := rfl

@[simp]
theorem liftedYonedaAddEquiv_comp {P Q : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v}}
    (η : P ⟶ Q) (X : C) (f : liftedRepresentable X ⟶ P) :
    liftedYonedaAddEquiv Q X (f ≫ η) =
      η.hom.app (op X) (liftedYonedaAddEquiv P X f) := rfl

/-- Lifted additive representables detect equality of natural transformations. -/
theorem liftedRepresentables_isSeparating :
    ObjectProperty.IsSeparating (.ofObj (liftedRepresentable (C := C))) := by
  intro P Q f g h
  apply ObjectProperty.hom_ext
  ext Y x
  have hh := h _ (ObjectProperty.ofObj_apply _ Y.unop)
    ((liftedYonedaAddEquiv P Y.unop).symm x)
  have he := congrArg (liftedYonedaAddEquiv Q Y.unop) hh
  simpa only [liftedYonedaAddEquiv_comp, AddEquiv.apply_symm_apply] using he

/-- The actual coproduct of lifted representables is a separator. -/
instance hasSeparator : HasSeparator (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v}) where
  hasSeparator := ⟨_, liftedRepresentables_isSeparating.isSeparator_coproduct⟩

end CategoryTheory.AdditiveFunctor
